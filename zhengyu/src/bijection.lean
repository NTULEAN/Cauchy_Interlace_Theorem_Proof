-- asymmetry since range is 
def isInv {u v: Type} (f: u -> v) (g: option v -> u) := ∀x: u, g $ f x = 