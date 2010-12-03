class WAM
  attr_accessor :code, :heap, :stack, :trail, :pdl, :args
  attr_accessor :p, :cp, :s, :hb, :b0, :b, :e
  def initialize
    @code  = []
    @heap  = []
    @stack = []
    @trail = []
    @pdl   = []
    @args  = []
  end
  
end

EnvFrame = Struct.new(:ce, :cp, :vars)
ChoiceFrame = Struct.new(:n, :args, :ce, :cp, :b, :bp, :tr, :h, :b0)

Var = String

Str = Struct.new(:name, :args) do
  def arity
    args.size
  end

  def to_s
    "#{name}(#{args.join(', ')})"
  end
  
  def inspect
    to_s
  end
end

def term?(t)
  Var === t or Str === t
end

module Registers
  class << self
    
    def flatten_program_term(p)
      flat = flatten_term p
      flat.map {|x| ref_term flat, x }
    end
  
    private
  
    def ref_term(ts, t)
      t.args.map! {|x| ts.index(x) } if Str === t
      t
    end
  
    def flatten_term(p)
      case p
        when Var then [p]
        when Str then ([p] + p.args.map{|x| flatten_term x}).flatten.uniq
        else          raise "Invalid term: #{p}"
      end
    end
  
  end
end