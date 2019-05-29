/* This file is included by symbol.c */

#include "id_table.h"

#ifndef ID_TABLE_DEBUG
#define ID_TABLE_DEBUG 0
#endif

#if ID_TABLE_DEBUG == 0
#define NDEBUG
#endif
#include "ruby_assert.h"

#define INITIAL_SIZE 8 // initial table size (if not set, calculated using round_capa)
#define LINEAR_PROBING // search nearby nodes for better cache consistency
#define GROW_SCALE 2 // how much the table grows on each rehash
#define MAX_LF 0.85 // maximum load factor allowed
#define NONE -1

#ifdef LINEAR_PROBING
#define INITIAL_R 4 // initial Hopscotch region
#endif

typedef rb_id_serial_t id_key_t;

static inline ID
key2id(id_key_t key)
{
    return rb_id_serial_to_id(key);
}

static inline id_key_t
id2key(ID id)
{
    return rb_id_to_serial(id);
}

static inline int
round_capa(int capa)
{
    // minsize is 4
    capa >>= 2;
    capa |= capa >> 1;
    capa |= capa >> 2;
    capa |= capa >> 4;
    capa |= capa >> 8;
    capa |= capa >> 16;
    return (capa + 1) << 2;
}

static inline unsigned int
fast_log2(unsigned int v){
    register unsigned int r; // result of log2(v) will go here
    register unsigned int shift;
    r =     (v > 0xFFFF) << 4; v >>= r;
    shift = (v > 0xFF  ) << 3; v >>= shift; r |= shift;
    shift = (v > 0xF   ) << 2; v >>= shift; r |= shift;
    shift = (v > 0x3   ) << 1; v >>= shift; r |= shift;
                                        r |= (v >> 1);
    return r;
}

enum {
    E, // empty
    L, // occupied: index==hash(key)
    S // rellocated: index!=hash(key)
};

typedef struct FLNode{
    unsigned char type; // how the node is used (E, L, S)
    int links[3]; // 0=prev/left, 1=next/right, 2=parent
    struct { // user data
        id_key_t key;
        VALUE value;
    } pair;
}FLNode; // 24 on x86, 32 on x64


struct rb_id_table{
    FLNode* table; // hash table
    int free_list; // list of free nodes (link to first free node)
    int N; // number of items in table
    int T; // table size
    #ifdef LINEAR_PROBING
    int R; // Hopscotch Region; limits number of iterations during linear probing
    #endif
};

typedef struct rb_id_table FLHashMap;

// calculate table load factor
static inline double loadFactor(FLHashMap* self){
    return (double)self->N / (double)self->T;
}

// maps between key and slot in table
static inline int hash(size_t key, size_t T){
	return key & (T-1);
	//return ((key>>(sizeof(key)/2))^key) & (T-1); // use this if key bit distribution is poor
}

// distance between a node's index and it's original hashed index: abs(idx-hash(key))
static inline int distIdx(size_t key, int idx, size_t T){
	int hidx = hash(key, T);
	int dist = hidx-idx;
	return (dist<0)? -1*dist : dist;
}

// private prototypes
static void clearTable(FLHashMap* self);
static int createTable(FLHashMap* self, int size);
static void resizeTable(FLHashMap* self);
static void addFreeNode(FLHashMap* self, int idx);
static void removeFreeNode(FLHashMap* self, int idx);
static int findFreeNode(FLHashMap* self, int parent);
static int rellocateNode(FLHashMap* self, int idx);
static int rellocateNodeTo(FLHashMap* self, int idx, int inode);

int rb_key_table_insert(struct rb_id_table *self, id_key_t key, VALUE val);
int rb_key_table_lookup(struct rb_id_table *self, id_key_t key, VALUE *valp);
int rb_key_table_delete(struct rb_id_table *self, id_key_t key);

// clear (initialize) the table
static void clearTable(FLHashMap* self){
    FLNode* table = self->table;
    self->N = 0;
    // initially, all nodes point to the immediate next (i+1) and prev (i-1)
    self->free_list = 0;
    for (int i=0; i<self->T; i++){
        table[i].type = E;
        table[i].links[0] = i-1; // will be -1 (NONE) on first node
        table[i].links[1] = i+1;
        table[i].links[2] = NONE;
    }
    table[self->T-1].links[1] = NONE; // last link has no next
}

// create (and intitialize) a table of given size
static int createTable(FLHashMap* self, int size){
    self->table = ZALLOC_N(FLNode, size);
    if (!self->table) return 0;
    self->T = size;
    clearTable(self);
    return 1;
}

// grow the table (rehash)
static void resizeTable(FLHashMap* self){
    int T = self->T;
    FLNode* table = self->table;
    createTable(self, T*GROW_SCALE); // create new table
    #ifdef LINEAR_PROBING
    self->R++; // increment Hopscotch region
    #endif
    for (int i=0; i<T; i++){ // rehash
        FLNode* node = &table[i];
        if (node->type ^ E){
            rb_key_table_insert(self, node->pair.key, node->pair.value);
        }
    }
    xfree(table);
}

// add node to free list
// this operation pushes the node to the top of free list 
static void addFreeNode(FLHashMap* self, int idx){
    self->N--;
    FLNode* dispose = &self->table[idx]; // update node links
    dispose->type = E;
    dispose->links[0] = NONE;
    dispose->links[1] = self->free_list;
    dispose->links[2] = NONE;
    if (self->free_list ^ NONE){
        self->table[self->free_list].links[0] = idx;
    }
    self->free_list = idx;
}

// remove a node from free list
static void removeFreeNode(FLHashMap* self, int idx){
    // adjust coalesced chain
    FLNode* table = self->table;
    FLNode* node = &table[idx];
    int iprev = node->links[0];
    int inext = node->links[1];
    if (iprev ^ NONE){
        FLNode* prev = &table[iprev];
        prev->links[1] = inext;
    }
    if (inext ^ NONE){
        FLNode* next = &table[inext];
        next->links[0] = iprev;
    }
    if (!(idx^self->free_list)){ // update free_list
        self->free_list = inext;
    }
}

// find a free node
// linear probing allows to find closeby nodes (+cache hits)
// hopscotch region limits probing to log(T) iterations
// free list guarantees always finding a free node even if probing fails, and it's done in O(1)
static int findFreeNode(FLHashMap* self, int parent){
	FLNode* table = self->table;
	int inode = NONE;
	FLNode* found = NULL;
	#ifdef LINEAR_PROBING
	for (int i=0; i<self->R; i++){ // at most log(T) probes
		if (parent+i>=self->T) break;
		int tmpi = parent+i; // search is done close to parent node (NOT necessarily close to hash(key))
		FLNode* tmp = &table[tmpi];
		if (!(tmp->type^E)){
			inode = tmpi;
			removeFreeNode(self, inode);
			found = tmp;
			break;
		}
	}
	#endif
    if (!(inode^NONE)){ // probing failed, use free list
    	inode = self->free_list;
    	found = &table[inode];
    	// adjust free list
		self->free_list = found->links[1];
		if (self->free_list ^ NONE){
		    table[self->free_list].links[0] = NONE;
		}
    }
	found->links[0] = NONE;
	found->links[1] = NONE;
	found->type = S;
	self->N++;
    return inode;
}

static int rellocateNode(FLHashMap* self, int idx){
	return rellocateNodeTo(self, idx, NONE);
}

// rellocate a given node to a new position, updating any and all links
static int rellocateNodeTo(FLHashMap* self, int idx, int inode){
    FLNode* table = self->table;
    FLNode* node = &table[idx];
    if (!(inode^NONE))
        inode = findFreeNode(self, node->links[2]);
    FLNode* used = &table[inode];
    // relloc data
    used->links[0] = node->links[0];
    used->links[1] = node->links[1];
    used->links[2] = node->links[2];
    used->pair.key = node->pair.key;
    used->pair.value = node->pair.value;
    // adjust links
    if (used->links[0] != NONE) table[used->links[0]].links[2] = inode;
    if (used->links[1] != NONE) table[used->links[1]].links[2] = inode;
    if (used->links[2] != NONE){
        FLNode* parent = &table[used->links[2]];
        if (parent->links[1]==idx) parent->links[1] = inode;
        else parent->links[0] = inode;
    }
    return inode;
}

struct rb_id_table *
rb_id_table_create(size_t capa)
{
    FLHashMap* self = ALLOC(struct rb_id_table);
    #ifdef INITIAL_SIZE
    int T = INITIAL_SIZE;
    #else
    int T = round_capa(capa);
    #endif
    createTable(self, T);
    #ifdef LINEAR_PROBING
    #ifdef INITIAL_SIZE
    self->R = INITIAL_R;
    #else
    self->R = fast_log2(T);
    #endif
    #endif
    return self;
}

void
rb_id_table_free(struct rb_id_table *self)
{
    xfree(self->table);
    xfree(self);
}

void
rb_id_table_clear(struct rb_id_table *self)
{
    clearTable(self);
}

size_t
rb_id_table_size(const struct rb_id_table *self)
{
    return (size_t)self->N;
}

size_t
rb_id_table_memsize(const struct rb_id_table *self)
{
    return sizeof(FLNode) * self->T + sizeof(struct rb_id_table);
}

#if ID_TABLE_DEBUG && 0
static void
hash_table_show(struct rb_id_table *self)
{
    int NE=0, NL=0, NS=0;
    FLNode* table = self->table;
    fprintf(stderr, "FL: %d[\n", self->free_list);
    for (int i=0; i<self->T; i++){
        FLNode* node = &table[i];
        fprintf(stderr, "    %d: ", i);
        switch (node->type){
            case E: fprintf(stderr, "E "); NE++; break;
            case L: fprintf(stderr, "L(%zu) ", node->pair.key); NL++; break;
            case S: fprintf(stderr, "S(%zu) ", node->pair.key); NS++; break;
        }
        fprintf(stderr, " <%d, %d> \n", node->links[0], node->links[1]);
    }
    fprintf(stderr, "\n]\n");
    fprintf(stderr, "T: %d\n", self->T);
    fprintf(stderr, "N: %d\n", self->N);
    #ifdef LINEAR_PROBING
    fprintf(stderr, "R: %d\n", self->R);
    #endif
    fprintf(stderr, "NE: %d/%d\n", NE, self->T-self->N);
    fprintf(stderr, "NL: %d\n", NL);
    fprintf(stderr, "NS: %d\n", NS);
    fprintf(stderr, "LF: %f\n", loadFactor(self));
    fprintf(stderr, "\n");
}
#endif

int
rb_key_table_lookup(struct rb_id_table *self, id_key_t key, VALUE *valp)
{
    FLNode* table = self->table;
    int idx = hash(key, self->T);
    FLNode* node = &table[idx];
    if (!(node->type ^ L)){ // only L types are considered (tree root), any other type = not found
        do{ // do a binary search
            if (node->pair.key == key){
                *valp = node->pair.value;
                return TRUE;
            }
            else{
                int ilink = (node->pair.key < key)&1;
                idx = node->links[ilink];
            }
            node = &table[idx];
        }while (idx^NONE);
    }
    return FALSE;
}

int
rb_id_table_lookup(struct rb_id_table *self, ID id, VALUE *valp)
{
    return rb_key_table_lookup(self, id2key(id), valp);
}

int
rb_key_table_insert(struct rb_id_table *self, id_key_t key, VALUE val)
{
    //return rb_id_table_insert_key(tbl, id2key(id), val);
    if (loadFactor(self) >= MAX_LF){
        resizeTable(self);
    }
    
    // calculate hash and operate on the resulting node
    FLNode* table = self->table;
    int idx = hash(key, self->T);
    FLNode* node = &table[idx];

    switch (node->type){
        case E: // empty node, insert data here
            {
            removeFreeNode(self, idx); // remove node from free list
            // store data and update type
            node->pair.key = key;
            node->pair.value = val;
            node->type = L;
            node->links[0] = NONE;
            node->links[1] = NONE;
            node->links[2] = NONE;
            self->N++;
            }
            break;
        case L: // occupied, search for the key and if not found add it
            {
            FLNode* cur = node;
            int parent = idx;
            do{ // we do a binary search, where links[0]=left and links[1]=right
            	  if (cur->pair.key == key){
                      cur->pair.value = val;
                      cur = NULL;
            	  }
            	  else{
            	      int ilink = (cur->pair.key < key)&1; // calculate which link to take
            	      if (cur->links[ilink] == NONE){
            	          int ichild = cur->links[ilink] = findFreeNode(self, parent);
            	          FLNode* child = &table[ichild];
            	          child->links[2] = parent;
                          child->pair.key = key;
                          child->pair.value = val;
            	          cur = NULL;
            	      }
            	      else{
            	          parent = cur->links[ilink];
            	          cur = &table[parent];
            	      }
            	  }
            }while (cur);
            }
            break;
        case S: // found item rellocated here, must push it (Cuckoo rellocate)
            {
            rellocateNode(self, idx);
            // change hashed node
            node->pair.key = key;
            node->pair.value = val;
            node->links[0] = NONE;
            node->links[1] = NONE;
            node->links[2] = NONE;
            node->type = L;
            }
            break;
    }
    return TRUE;
}

int
rb_id_table_insert(struct rb_id_table *self, ID id, VALUE val)
{
    return rb_key_table_insert(self, id2key(id), val);
}

// delete a node by index using binary tree algorithm
// if another node is relocated here it's older index will be returned, NONE otherwise
static int FLtable_del_at(struct rb_id_table *self, FLNode* table, FLNode* node, int idx, int ilink){
    int ichild = NONE;
    int relocated = NONE;
    int t = 1;
    if (node->links[(t^=1)] == NONE || node->links[(t^=1)] == NONE){ // at most one child
        ichild = node->links[(t^=1)];
        int p = node->links[2];
        if (ichild ^ NONE) table[ichild].links[2] = p;
        switch (((p^NONE)|!(ichild^NONE))){
            case 0:
                relocated = ichild;
                rellocateNodeTo(self, ichild, idx);
                addFreeNode(self, ichild);
                break;
            default:
                if (p^NONE) table[p].links[ilink] = ichild;
                addFreeNode(self, idx);
        }
    }
    else{ // two children
        int p = idx;
        int aux = node->links[1];
        int iaux;
        while ((iaux=table[aux].links[0])^NONE){
            p = aux;
            aux = iaux;
        }
        ichild = table[aux].links[1];
        node->pair.value = table[aux].pair.value;
        node->pair.key = table[aux].pair.key;
        if (p ^ idx){
            table[p].links[0] = ichild;
            if (ichild!=NONE) table[ichild].links[2] = p;
        }
        else{
            node->links[1] = ichild;
            if (ichild!=NONE) table[ichild].links[2] = idx;
        }
        relocated = aux;
        addFreeNode(self, aux);
    }
    return relocated;
}

int
rb_key_table_delete(struct rb_id_table *self, id_key_t key)
{
    FLNode* table = self->table;
    int idx = hash(key, self->T);
    FLNode* node = &table[idx];
    int ilink = 0;
    if (node->type == L){ // only consider L types (tree root)
        do{ // binary search
            if (node->pair.key == key){ // binary tree delete
                FLtable_del_at(self, table, node, idx, ilink);
                return TRUE;
            }
            else{
                ilink = (node->pair.key < key)&1;
                idx = node->links[ilink];
            }
            node = &table[idx];
        }while (idx^NONE);
    }
    return FALSE;
}

int
rb_id_table_delete(struct rb_id_table *self, ID id)
{
    return rb_key_table_delete(self, id2key(id));
}

void
rb_id_table_foreach_with_replace(struct rb_id_table *self, rb_id_table_foreach_func_t *func, rb_id_table_update_callback_func_t *replace, void *data)
{
    int i, capa = self->T;
    FLNode* table = self->table;
    for (i=0; i<capa; i++) {
        if (table[i].type != E){
            const id_key_t key = table[i].pair.key;
            enum rb_id_table_iterator_result ret = (*func)(Qundef, table[i].pair.value, data);
            assert(key != 0);

            if (ret == ID_TABLE_REPLACE) {
                VALUE val = table[i].pair.value;
                ret = (*replace)(NULL, &val, data, TRUE);
                table[i].pair.value = val;
            }
            else if (ret == ID_TABLE_STOP)
                return;
        }
    }
}

void
rb_id_table_foreach(struct rb_id_table *self, rb_id_table_foreach_func_t *func, void *data)
{
    int i, capa = self->T;
    FLNode* table = self->table;
    for (i=0; i<capa;) {
	if (table[i].type != E){
	    FLNode* node = &table[i];
	    const id_key_t key = node->pair.key;
	    enum rb_id_table_iterator_result ret = (*func)(key2id(key), node->pair.value, data);
	    assert(key != 0);

	    if (ret == ID_TABLE_DELETE){
	        int ilink = (node->links[2]==NONE)? 0 : (table[node->links[2]].pair.key < node->pair.key)&1;
	        int relocated = FLtable_del_at(self, table, node, i, ilink);
	        if (relocated > i) continue; // recheck this slot
	    }
	    else if (ret == ID_TABLE_STOP)
		    break;
	}
	i++;
    }
}

void
rb_id_table_foreach_values(struct rb_id_table *self, rb_id_table_foreach_values_func_t *func, void *data)
{
    int i, capa = self->T;
    FLNode* table = self->table;
    for (i=0; i<capa;) {
	if (table[i].type != E){
	    FLNode* node = &table[i];
	    enum rb_id_table_iterator_result ret = (*func)(node->pair.value, data);

	    if (ret == ID_TABLE_DELETE){
	        int ilink = (node->links[2]==NONE)? 0 : (table[node->links[2]].pair.key < node->pair.key)&1;
	        int relocated = FLtable_del_at(self, table, node, i, ilink);
	        if (relocated > i) continue; // recheck this slot
	    }
	    else if (ret == ID_TABLE_STOP)
		    return;
	}
	i++;
    }
}
