import linear_algebra.matrix
import data.matrix.basis
import data.polynomial


def curry (a b y: Type*) (f: a × b -> y) : a -> b -> y :=
  begin
    intros aa bb,
    exact f (aa, bb),
  end
#print curry

def curry2 (a b y: Type*) (f: a × b -> y) : a -> b -> y :=
  λ (x1: a) (x2: b), f (x1, x2)

constants (x: nat)
variables (y: nat)
section testSection 
  #print x
  variable (p: Prop)
  theorem test1: p \/ ¬p := begin
    exact classical.em p
  end 
end testSection

namespace testSection2
  variable (p: Prop)
  theorem test1: p \/ ¬p := begin
    exact classical.em p
  end 
end testSection2

