/-
b725 -- (R335)(4)(iv): THE C2 STATEMENT AND ROUTE (B)'S PER-FIELD CERTIFICATES. Vanilla Lean 4 (Int, Nat, List; no imports, no
Mathlib, no native_decide).

  * The statement's definitions as data/b722_c2_statement.txt writes them (walk, pform, rQ, aQ, F, bL), and the statement as a Prop,
    `C2ValueLaw` (its E0 grade DERIVES, read before any proof: relay data/b725_c2.txt).
  * Route (B): the sweep table (the box [-s, s]², s the least with s * s > 2N), Omega by trial division, and the table
    W(n) = Omega(n) · L · b(n) by the Omega recursion W(n) = Omega(n) · L · a(n) - SUM over d | n, 1 < d < n, of W(d) · a(n / d).
  * (L1) and (L2) as Props: what joins the certificates to the statement. Not proved here.
  * The eighteen certificates `cert D n0 v q = true`, each by `decide +kernel` under a heartbeat cap, a traced sorry its fallback, one
    module per field from b726 ((R336)(3)): SIDEExplicitFormula/C2Field/M<|D|>.lean, one dispatch per field.
    The route is mirrored in Python at 18 of 18 against the statement's own values (relay tools/b725_c2.py).
Every loop carries its own fuel (structural recursion); each loop over a table matches the table at every step, so the kernel holds
each step's table at its head before the next.
-/

namespace C2Walk

/-! ## The statement's definitions, as data/b722_c2_statement.txt writes them -/

/-- the walk: (D, n0, v, q) -- at the discriminant D the least n with b(n) < 0 is n0 and b(n0) = v / q.
    The eighteen imaginary quadratic fields of class number 2 (completeness: Baker 1971, Stark 1975; cited, not compiled). -/
def walk : List (Int × Nat × Int × Nat) :=
  [(-15, 24, -2, 1),
   (-20, 36, -2, 1),
   (-24, 36, -1, 2),
   (-35, 135, -2, 1),
   (-40, 100, -1, 2),
   (-51, 225, -2, 1),
   (-52, 196, -2, 1),
   (-88, 484, -1, 2),
   (-91, 875, -2, 1),
   (-115, 1225, -2, 1),
   (-123, 1089, -2, 1),
   (-148, 1444, -2, 1),
   (-187, 3773, -2, 1),
   (-232, 3364, -1, 2),
   (-235, 4225, -2, 1),
   (-267, 4761, -2, 1),
   (-403, 17303, -2, 1),
   (-427, 14161, -2, 1)]

/-- the principal form of discriminant D < 0, D ≡ 0 or 1 mod 4: x² + D·y²/(-4) or x² + xy + (1 - D)/4 · y² -/
def pform (D x y : Int) : Int :=
  if D % 4 = 0 then x * x + (-D / 4) * y * y else x * x + x * y + ((1 - D) / 4) * y * y

/-- r_Q(n): the number of (x, y) with Q(x, y) = n, by finite enumeration over the box [-n, n]² (every representation lies in it,
    since Q(x, y) ≥ (x² + y²)/2 for the principal form of D < -4) -/
def rQ (D : Int) (n : Nat) : Nat :=
  ((List.range (2 * n + 1)).flatMap fun i => (List.range (2 * n + 1)).map fun j => ((i : Int) - n, (j : Int) - n)).countP
    fun p => decide (pform D p.1 p.2 = (n : Int))

/-- a(n) = r_Q(n) / 2 (two units) -/
def aQ (D : Int) (n : Nat) : Int := (rQ D n : Int) / 2

/-- F D k n: the sum over the ordered factorizations n = d₁ ⋯ d_k, every dᵢ ≥ 2, of a(d₁) ⋯ a(d_k) -/
def F (D : Int) : Nat → Nat → Int
  | 0, n => if n = 1 then 1 else 0
  | k + 1, n => ((List.range (n + 1)).filter fun d => decide (2 ≤ d ∧ n % d = 0)).foldl (fun s d => s + aQ D d * F D k (n / d)) 0

/-- L · b(n), L = 360360 = lcm(1, …, 15): b(n), the coefficient of n^-s in log(Z_Q / 2), is SUM over k ≥ 1 of (-1)^(k+1) F_k(n) / k,
    and k ≤ 15 for n < 2^16 -/
def bL (D : Int) (n : Nat) : Int :=
  (List.range 15).foldl (fun s i => s + (if i % 2 = 0 then 1 else -1) * (360360 / ((i : Int) + 1)) * F D (i + 1) n) 0

/-- THE C2 VALUE LAW AT THE LEAST NEGATIVE INDEX, at each field of the list: b(n0) = v / q, and b(n) ≥ 0 for 2 ≤ n < n0.
    (data/b722_c2_statement.txt's `theorem c2_value_law`, its binders taken under one ∀.) -/
def C2ValueLaw : Prop :=
  ∀ (D : Int) (n0 : Nat) (v : Int) (q : Nat), (D, n0, v, q) ∈ walk →
    ((q : Int) * bL D n0 = v * 360360) ∧ ∀ n, 2 ≤ n → n < n0 → 0 ≤ bL D n

/-! ## Route (B): a table keyed by Nat (root 0; n odd to the left at n / 2, n even to the right at n / 2 - 1) -/

inductive Tab where
  | leaf : Tab
  | node : Tab → Int → Tab → Tab

def Tab.get : Tab → Nat → Int
  | Tab.leaf, _ => 0
  | Tab.node l x r, n => if n = 0 then x else if n % 2 = 1 then Tab.get l (n / 2) else Tab.get r (n / 2 - 1)

def Tab.lft : Tab → Tab
  | Tab.leaf => Tab.leaf
  | Tab.node l _ _ => l

def Tab.val : Tab → Int
  | Tab.leaf => 0
  | Tab.node _ x _ => x

def Tab.rgt : Tab → Tab
  | Tab.leaf => Tab.leaf
  | Tab.node _ _ r => r

/-- the table with x at n; the fuel is the depth (64 is past every index here) -/
def Tab.set : Nat → Tab → Nat → Int → Tab
  | 0, t, _, _ => t
  | k + 1, t, n, x =>
    if n = 0 then Tab.node (Tab.lft t) x (Tab.rgt t)
    else if n % 2 = 1 then Tab.node (Tab.set k (Tab.lft t) (n / 2) x) (Tab.val t) (Tab.rgt t)
    else Tab.node (Tab.lft t) (Tab.val t) (Tab.set k (Tab.rgt t) (n / 2 - 1) x)

/-- one point of the sweep: r(v) + 1 where v = Q(x, y) lies in [0, N] -/
def bump (D : Int) (N : Nat) (x y : Int) (t : Tab) : Tab :=
  if 0 ≤ pform D x y ∧ pform D x y ≤ (N : Int) then
    Tab.set 64 t (pform D x y).toNat (Tab.get t (pform D x y).toNat + 1)
  else t

def sweepRow (D : Int) (N : Nat) (x : Int) : Nat → Int → Tab → Tab
  | 0, _, t => t
  | k + 1, y, t =>
    match bump D N x y t with
    | Tab.leaf => sweepRow D N x k (y + 1) Tab.leaf
    | Tab.node l c r => sweepRow D N x k (y + 1) (Tab.node l c r)

def sweepAll (D : Int) (N s : Nat) : Nat → Int → Tab → Tab
  | 0, _, t => t
  | k + 1, x, t =>
    match sweepRow D N x (2 * s + 1) (-(s : Int)) t with
    | Tab.leaf => sweepAll D N s k (x + 1) Tab.leaf
    | Tab.node l c r => sweepAll D N s k (x + 1) (Tab.node l c r)

def sideAux (N : Nat) : Nat → Nat → Nat
  | 0, s => s
  | k + 1, s => if 2 * N < s * s then s else sideAux N k (s + 1)

/-- the least s with s * s > 2N -/
def side (N : Nat) : Nat := sideAux N (2 * N + 2) 0

/-- the sweep's table: r_Q(n) for n ≤ N, over the box [-s, s]² -/
def rTab (D : Int) (N : Nat) : Tab :=
  sweepAll D N (side N) (2 * side N + 1) (-(side N : Int)) Tab.leaf

/-- Omega by trial division from p, the fuel bounding the steps -/
def omegaAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, n, p =>
    if n < 2 then 0
    else if n < p * p then 1
    else if n % p = 0 then omegaAux f (n / p) p + 1
    else omegaAux f n (p + 1)

/-- Omega(n), the prime factors of n with multiplicity -/
def bigOmega (n : Nat) : Nat := omegaAux (n + 1) n 2

/-- SUM over d | n, 2 ≤ d, d * d ≤ n, of W(d) a(n / d), and W(n / d) a(d) where n / d ≠ d: the divisors 1 < d < n, each once -/
def divSum (a : Nat → Int) (W : Tab) (n : Nat) : Nat → Nat → Int → Int
  | 0, _, s => s
  | f + 1, d, s =>
    if n < d * d then s
    else if n % d = 0 then
      divSum a W n f (d + 1)
        (if n / d = d then s + Tab.get W d * a d
         else s + Tab.get W d * a (n / d) + Tab.get W (n / d) * a d)
    else divSum a W n f (d + 1) s

/-- W(n) = Omega(n) · L · a(n) - divSum -/
def wStep (a : Nat → Int) (W : Tab) (n : Nat) : Int :=
  (bigOmega n : Int) * 360360 * a n - divSum a W n n 2 0

def wLoop (a : Nat → Int) : Nat → Nat → Tab → Tab
  | 0, _, W => W
  | k + 1, n, W =>
    match Tab.set 64 W n (wStep a W n) with
    | Tab.leaf => wLoop a k (n + 1) Tab.leaf
    | Tab.node l c r => wLoop a k (n + 1) (Tab.node l c r)

/-- the table of W(n) = Omega(n) · L · b(n) for 2 ≤ n ≤ N -/
def wTab (a : Nat → Int) (N : Nat) : Tab := wLoop a (N - 1) 2 Tab.leaf

def allNonneg (W : Tab) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, n => if 0 ≤ Tab.get W n then allNonneg W k (n + 1) else false

/-- a(m) read from the sweep's table -/
def aOf (r : Tab) (m : Nat) : Int := Tab.get r m / 2

/-- the certificate at one field: Omega(n0) divides W(n0), q · (W(n0) / Omega(n0)) = v · L, and W(n) ≥ 0 for 2 ≤ n < n0 -/
def cert (D : Int) (n0 : Nat) (v : Int) (q : Nat) : Bool :=
  Tab.get (wTab (aOf (rTab D n0)) n0) n0 % (bigOmega n0 : Int) == 0 &&
  (q : Int) * (Tab.get (wTab (aOf (rTab D n0)) n0) n0 / (bigOmega n0 : Int)) == v * 360360 &&
  allNonneg (wTab (aOf (rTab D n0)) n0) (n0 - 2) 2

/-! ## What joins the certificates to the statement: two Props, not proved here -/

/-- (L1) the sweep's table is r_Q on [0, n0] at each field of the walk -/
def L1 : Prop :=
  ∀ (D : Int) (n0 : Nat) (v : Int) (q : Nat), (D, n0, v, q) ∈ walk → ∀ n, n ≤ n0 → Tab.get (rTab D n0) n = (rQ D n : Int)

/-- (L2) the Omega recursion is the ordered-factorization sum: W(n) = Omega(n) · bL(n) for 2 ≤ n ≤ N < 2^16 -/
def L2 : Prop :=
  ∀ (D : Int) (N n : Nat), N < 65536 → 2 ≤ n → n ≤ N → Tab.get (wTab (aQ D) N) n = (bigOmega n : Int) * bL D n

/-! ## The eighteen certificates stand one module each, SIDEExplicitFormula/C2Field/M<|D|>.lean (b726, (R336)(3)) -/

end C2Walk
