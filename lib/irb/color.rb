# frozen_string_literal: true
require 'reline'
require 'ripper'

module IRB # :nodoc:
  module Color
    CLEAR     = 0
    BOLD      = 1
    UNDERLINE = 4
    REVERSE   = 7
    RED       = 31
    GREEN     = 32
    YELLOW    = 33
    BLUE      = 34
    MAGENTA   = 35
    CYAN      = 36

    TOKEN_KEYWORDS = {
      on_kw: ['nil', 'self', 'true', 'false', '__FILE__', '__LINE__'],
      on_const: ['ENV'],
    }
    private_constant :TOKEN_KEYWORDS

    # A constant of all-bit 1 to match any Ripper's state in #dispatch_seq
    ALL = -1
    private_constant :ALL

    begin
      # Following pry's colors where possible, but sometimes having a compromise like making
      # backtick and regexp as red (string's color, because they're sharing tokens).
      TOKEN_SEQ_EXPRS = {
        on_CHAR:            [[BLUE, BOLD],            ALL],
        on_backtick:        [[RED],                   ALL],
        on_comment:         [[BLUE, BOLD],            ALL],
        on_const:           [[BLUE, BOLD, UNDERLINE], ALL],
        on_embexpr_beg:     [[RED],                   ALL],
        on_embexpr_end:     [[RED],                   ALL],
        on_embvar:          [[RED],                   ALL],
        on_float:           [[MAGENTA, BOLD],         ALL],
        on_gvar:            [[GREEN, BOLD],           ALL],
        on_heredoc_beg:     [[RED],                   ALL],
        on_heredoc_end:     [[RED],                   ALL],
        on_ident:           [[BLUE, BOLD],            Ripper::EXPR_ENDFN],
        on_imaginary:       [[BLUE, BOLD],            ALL],
        on_int:             [[BLUE, BOLD],            ALL],
        on_kw:              [[GREEN],                 ALL],
        on_label:           [[MAGENTA],               ALL],
        on_label_end:       [[RED],                   ALL],
        on_qsymbols_beg:    [[RED],                   ALL],
        on_qwords_beg:      [[RED],                   ALL],
        on_rational:        [[BLUE, BOLD],            ALL],
        on_regexp_beg:      [[RED, BOLD],             ALL],
        on_regexp_end:      [[RED, BOLD],             ALL],
        on_symbeg:          [[YELLOW],                ALL],
        on_tstring_beg:     [[RED],                   ALL],
        on_tstring_content: [[RED],                   ALL],
        on_tstring_end:     [[RED],                   ALL],
        on_words_beg:       [[RED],                   ALL],
        on_parse_error:     [[RED, REVERSE],          ALL],
        compile_error:      [[RED, REVERSE],          ALL],
      }
    rescue NameError
      # Give up highlighting Ripper-incompatible older Ruby
      TOKEN_SEQ_EXPRS = {}
    end
    private_constant :TOKEN_SEQ_EXPRS

    class << self
      def colorable?
        $stdout.tty? && (/mswin|mingw/ =~ RUBY_PLATFORM || (ENV.key?('TERM') && ENV['TERM'] != 'dumb'))
      end

      def inspect_colorable?(obj)
        case obj
        when String, Symbol, Regexp, Integer, Float, FalseClass, TrueClass, NilClass
          true
        when Hash
          obj.all? { |k, v| inspect_colorable?(k) && inspect_colorable?(v) }
        when Array
          obj.all? { |o| inspect_colorable?(o) }
        when Range
          inspect_colorable?(obj.begin) && inspect_colorable?(obj.end)
        when Module
          !obj.name.nil?
        else
          false
        end
      end

      def clear
        return '' unless colorable?
        "\e[#{CLEAR}m"
      end

      def colorize(text, seq)
        return text unless colorable?
        seq = seq.map { |s| "\e[#{const_get(s)}m" }.join('')
        "#{seq}#{text}#{clear}"
      end

      def scan(code)
        Ripper::Lexer.new(code).scan
      end

      def colorize_code(code)
        return code unless colorable?

        symbol_state = SymbolState.new
        colored = +''
        length = 0
        pos = [1, 0]

        scan(code).each do |elem|
          token = elem.event
          str = elem.tok
          expr = elem.state
          in_symbol = symbol_state.scan_token(token)
          next if ([elem.pos[0], elem.pos[1] + str.bytesize] <=> pos) <= 0
          str.each_line do |line|
            if line.end_with?("\n")
              pos[0] += 1
              pos[1] = 0
            else
              pos[1] += line.bytesize
            end
            line = Reline::Unicode.escape_for_print(line)
            if seq = dispatch_seq(token, expr, line, in_symbol: in_symbol)
              colored << seq.map { |s| "\e[#{s}m" }.join('')
              colored << line.sub(/\Z/, clear)
            else
              colored << line
            end
          end
          length += str.bytesize
        end

        # give up colorizing incomplete Ripper tokens
        return code if length != code.bytesize

        colored
      end

      private

      def dispatch_seq(token, expr, str, in_symbol:)
        if token == :on_parse_error or token == :compile_error
          TOKEN_SEQ_EXPRS[token][0]
        elsif in_symbol
          [YELLOW]
        elsif TOKEN_KEYWORDS.fetch(token, []).include?(str)
          [CYAN, BOLD]
        elsif (seq, exprs = TOKEN_SEQ_EXPRS[token]; (expr & (exprs || 0)) != 0)
          seq
        else
          nil
        end
      end
    end

    # A class to manage a state to know whether the current token is for Symbol or not.
    class SymbolState
      def initialize
        # Push `true` to detect Symbol. `false` to increase the nest level for non-Symbol.
        @stack = []
      end

      # Return true if the token is a part of Symbol.
      def scan_token(token)
        prev_state = @stack.last
        case token
        when :on_symbeg
          @stack << true
        when :on_ident, :on_op, :on_const, :on_ivar, :on_cvar, :on_gvar, :on_kw
          if @stack.last # Pop only when it's Symbol
            @stack.pop
            return prev_state
          end
        when :on_tstring_beg
          @stack << false
        when :on_embexpr_beg
          @stack << false
          return prev_state
        when :on_tstring_end # :on_tstring_end may close Symbol
          @stack.pop
          return prev_state
        when :on_embexpr_end
          @stack.pop
        end
        @stack.last
      end
    end
    private_constant :SymbolState
  end
end
