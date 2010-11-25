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