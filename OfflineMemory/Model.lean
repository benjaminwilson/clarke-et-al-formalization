namespace OfflineMemory

variable {n : Nat} {V : Type} [DecidableEq V]

abbrev ValueTimestamp V := V × Nat
abbrev AddrValueTimestamp n V := Fin n × ValueTimestamp V
abbrev Multiplicities n V := AddrValueTimestamp n V → Nat

/-- Kronecker delta function. Returns 1 if x = y, 0 otherwise. -/
def delta {α : Type} [DecidableEq α] (x y : α) : Nat := if x = y then 1 else 0

/-- The state of the Checker, as per the paper, but augmented with `last` for the purposes of verification. -/
structure State n V where
  /-- The number of times each AddrValueTimestamp has been returned by the untrusted RAM -/
  reads: Multiplicities n V
  /-- The number of times that the RAM has been _asked_ to write each AddrValueTimestamp (whatever it actually wrote) -/
  writes: Multiplicities n V
  timer: Nat
  /-- For each memory address, the ValueTimestamp that the checker _asked_ the RAM to write. -/
  last: Fin n → ValueTimestamp V

/-- The State after running the paper's initialize(), modified to allow for arbitrary initialization values. -/
def initialState (initialValues: Fin n → V) : State n V where
  reads := fun _ => 0
  writes := fun (a, (v, t)) => delta (v, t) ((initialValues a), 0)
  timer := 0
  last := fun a => (initialValues a, 0)

/-- The State after running the paper's get(a), where resp is the response given by the RAM. -/
def get (s: State n V) (a : Fin n) (resp: ValueTimestamp V) : State n V :=
  { s with
      reads := fun x => s.reads x + delta x (a, resp)
      timer := max s.timer (resp.2 + 1) }

/-- The State after running the paper's put(a, v). -/
def put (s: State n V) (a : Fin n) (v : V) : State n V :=
  { s with
      writes := fun x => s.writes x + delta x (a, (v, s.timer))
      last := fun a' => if a' = a then (v, s.timer) else s.last a' }

/-- The common get then put pattern of load(a) and store(a, v). `resp` is the
response to get while `v` is the value value purportedly written back to RAM. -/
def getPut (s : State n V) (a : Fin n) (resp : ValueTimestamp V) (v : V) : State n V :=
  put (get s a resp) a v

/-- Represents the load(a) and store(a, v) operations of the paper where in both cases `reply` is the ValueTimestamp returned by the paper's get() -/
inductive OpEnum (V : Type) where
  | load
  | store (v: V)
  deriving DecidableEq, Repr

/-- Represents the load(a) and store(a, v) operations of the paper where in both cases `reply` is the ValueTimestamp returned by the paper's get(), along with the RAM's response to the get() -/
structure OpResponse n V where
  address: Fin n
  resp: ValueTimestamp V
  type: OpEnum V
  deriving DecidableEq, Repr

/-- The value (purportedly) written to RAM by an operation via its put(). -/
def OpResponse.valueWritten (op: OpResponse n V) : V :=
  match op.type with
  | .load => op.resp.1
  | .store v => v

/-- The State after performing a load() or store() operation and processing the RAM's response. -/
def step (s : State n V) (op: OpResponse n V) : State n V :=
  getPut s op.address op.resp op.valueWritten

/-- Maximum of the final replies' timestamps. -/
def timestampMax (resps : Fin n → ValueTimestamp V) : Nat :=
  (List.ofFn fun a => (resps a).2).foldr max 0

/-- The State after calling check(), assuming the RAM responds with `resps`. -/
def check (s : State n V) (resps : Fin n → ValueTimestamp V) : State n V :=
  { s with reads := fun x => s.reads x + delta (resps x.1) x.2
           timer := max s.timer ((timestampMax resps) + 1) }

/-- Corresponds to A_i in our exposition, where s is the state after operation E_i -/
def Matched (s : State n V) : Prop :=
  ∀ x, s.writes x = s.reads x + delta (s.last x.1) x.2

/-- Corresponds to B_i in our exposition, where s is the state after operation E_i -/
def Unmatched (s : State n V) : Prop :=
  ∃ x, (s.reads x > s.writes x) ∧ (x.2.2 < s.timer)

/-- Acceptance, information-theoretic (i.e. not hashing). -/
def Accepts (s : State n V) : Prop :=
  ∀ x, s.reads x = s.writes x

/-- "Execute" the OpResponses; does not initialize() or check() -/
def run (s : State n V) : List (OpResponse n V) → State n V
  | [] => s
  | op :: ops => run (step s op) ops

/-- Iff RAM was honest during check(); this is H_{k+1} in the exposition. -/
def CheckIsHonest (s: State n V) (resps: Fin n → ValueTimestamp V) : Prop :=
  ∀ a, resps a = s.last a

/-- Iff the OpResponse honest, given the current state `s`, i.e. did it return the last value written to that address?
This corresponds to the statement H_i from our handwritten proof via
H_i ↔ Honest (state i-1) (operation E_i)
-/
def Honest (s : State n V) (op: OpResponse n V) : Prop :=
  s.last op.address = op.resp

/-- Repeated conjunctive application of Honest over all operations. -/
def AllHonest (s : State n V) : List (OpResponse n V) → Prop
  | [] => True
  | op :: ops => Honest s op ∧ AllHonest (step s op) ops

/-- Honesty of all `E_1,...,E_{k+1}` (so including check()) (note that E_0 =
initialize() can not be dishonest, by definition). -/
def ExecutionHonest (initialValues : Fin n → V) (ops : List (OpResponse n V))
    (replies : Fin n → ValueTimestamp V) : Prop :=
  AllHonest (initialState initialValues) ops ∧
  CheckIsHonest (run (initialState initialValues) ops) replies

end OfflineMemory
