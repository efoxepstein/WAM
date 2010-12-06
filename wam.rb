require 'set'

class WAM
  attr_accessor :code, :heap, :stack, :trail, :pdl, :args,
                :p, :cp, :s, :hb, :b0, :b, :e, :mode, :seen
  
  def initialize
    @code  = []
    @heap  = []
    @stack = []
    @trail = []
    @pdl   = []
    @args  = []
    
    mode = :write
  end
  
  def compile_from_registers(regs)
    @seen = Set.new
    regs.each {|r| compile_register r }
  end
  
  def compile_register(reg)
#    puts "compile_register(#{reg.class.name})"
    if Str === reg
      get_structure reg.name
      reg.args.each {|r| compile_register r }
    elsif @seen.include? reg
      unify_value reg
    else
      @seen << reg
      unify_variable reg
    end
  end
  
  def get_structure(reg)
    puts "get_structure #{reg}"
  end
  
  def unify_variable(reg)
    puts "unify_variable #{reg}"
  end
  
  def unify_value(reg)
    puts "unify_value #{reg}"
  end
end

EnvFrame = Struct.new(:ce, :cp, :vars)
ChoiceFrame = Struct.new(:n, :args, :ce, :cp, :b, :bp, :tr, :h, :b0)

Var = String

class Str
  attr_accessor :args, :name
  
  def self.[](*args)
    new(*args)
  end
  
  def initialize(nombre, blargs = [])
    self.name = nombre
    self.args = blargs
  end
  
  def arity
    args.size
  end

  def to_s
    args.empty? ? name : "#{name}(#{args.map(&:to_s).join(', ')})"
  end
  
  def eql?(str)
    args === str.args and name === str.name
  end
  
  def equal?(x) ; eql?(x) ; end
  def ==(x) ; eql?(x) ; end
  
  def hash
    [name, args].hash
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
    
    def ref_term(ts, t)
      if Str === t
        Str[t.name, t.args.map {|x| ts.index(x) } ]
      else
        t.clone
      end
    end
    
    def flatten_term(p)
      case p
        when Var then [p.clone]
        when Str
          args = p.args.map{|x| flatten_term x}
          ([p.clone] + args).flatten.uniq
        else          raise "Invalid term: #{p}"
      end
    end
  
  end
end

# f(x, g(x), x) ==> [f(1, 2, 1), "x", g(1)]
GOOD_TERM = Str.new('f', ['x', Str.new('g',['x']), 'x'])

ADD_FACT = Str['add', [Str['o'], Str['s', [Str['o']]], Str['s', [Str['o']]]]]
