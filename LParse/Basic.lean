inductive DCont (ε α) where
  | Intro (run : (ρ : Type u) → (α → ρ) → (ε → ρ) → ρ)

@[simp]
def run {ε α} (c : DCont ε α) := match c with
  | DCont.Intro r => r

instance {ε : Type u} : Functor (DCont ε) where
  map f c := DCont.Intro (λ ρ => λ bf => λ ef => run c ρ (bf ∘ f) ef)

instance {ε : Type u} : Applicative (DCont ε) where
  pure a := DCont.Intro (λ _ => λ af => λ _ => af a)
  seq cf ca := DCont.Intro (λ ρ => λ bf => λ ef => run cf ρ (λ f => run (ca ()) ρ (bf ∘ f) ef) ef)

@[simp]
def throw {ε α} (e : ε) : DCont ε α := DCont.Intro (λ _ => λ _ => λ ef => ef e)

instance {ε : Type u} [Inhabited ε] : Alternative (DCont ε) where
  failure := DCont.Intro (λ _ => λ _ => λ ef => ef Inhabited.default)
  orElse ca cb := DCont.Intro (λρ => λaf => λef => run ca ρ af (λ_ => run (cb ()) ρ af ef))

instance {ε : Type u} : Monad (DCont ε) where
  bind x f := DCont.Intro (λρ => λbf => λef => run x ρ (λc => run (f c) ρ bf ef) ef)

theorem dcont_id {α β ε} : ∀ (a : α) (f : α → β) (e : ε → β), run (pure f <*> pure a) β id e = f a := by simp

inductive SafeParser (τ : Type u) (P : List τ → List τ → Prop) (α : Type v) where
  | Intro (pFunc : (tIn : List τ) → DCont String (α × {tOut : List τ // P tIn tOut}))

def pFunc {τ α P} (p : SafeParser τ P α) := match p with
  | SafeParser.Intro f => f

def weakenParser {τ α P} (p : SafeParser τ P α) (P' : List τ → List τ → Prop) (H : ∀t t', P t t' → P' t t') :=
  let p'Func : (tIn : List τ) → DCont String (α × {tOut : List τ // P' tIn tOut}) := by
    intro tIn
    exact (λ(res,r) => (res,Subtype.mk r.val (H tIn r.val r.property))) <$> pFunc p tIn
  SafeParser.Intro p'Func

def Parser (τ : Type u) (α : Type v) := SafeParser τ (λtIn => λtOut => tOut.length <= tIn.length) α

def StrongParser (τ : Type u) (α : Type v) := SafeParser τ (λtIn => λtOut => tOut.length < tIn.length) α

def weakenParser_SP {τ α} (p : StrongParser τ α) : Parser τ α :=
  let p'Func := by
    intro tIn
    exact (λ(res,r) => (res,Subtype.mk r.val (by grind))) <$> pFunc p tIn
  SafeParser.Intro p'Func

instance {τ : Type u} : Functor (Parser τ) where
  map {α β} (f : α → β) p :=
    let pf := λt => (λ(a,b) => (f a,b)) <$> pFunc p t
    SafeParser.Intro pf

instance {τ : Type u} : Functor (StrongParser τ) where
  map {α β} (f : α → β) p :=
    let pf := λt => (λ(a,b) => (f a,b)) <$> pFunc p t
    SafeParser.Intro pf

instance {τ : Type u} : Applicative (Parser τ) where
  pure a :=
    let lt (t : List τ) : { t' : List τ // t'.length <= t.length } := Subtype.mk t (by simp)
    SafeParser.Intro (λt => pure (a,lt t))
  seq pf pa :=
  let pfnc :=(λt =>
    let cf := pFunc pf t
    cf >>= (λ(f,r) => (λ(a,b) => (f a, Subtype.mk b.val (by grind))) <$> pFunc (pa ()) r)
    )
  SafeParser.Intro pfnc

instance {τ : Type u} : Seq (StrongParser τ) where
  seq pf pa :=
  let pfnc :=(λt =>
    let cf := pFunc pf t
    cf >>= (λ(f,r) => (λ(a,b) => (f a, Subtype.mk b.val (by grind))) <$> pFunc (pa ()) r)
    )
  SafeParser.Intro pfnc

instance {τ : Type u} : Alternative (Parser τ) where
  failure := SafeParser.Intro (λ_ => throw "No choice!")
  orElse pa pb := SafeParser.Intro (λt => pFunc pa t <|> pFunc (pb ()) t)

instance {τ : Type u} {α : Type v} : OrElse (StrongParser τ α) where
  orElse pa pb := SafeParser.Intro (λt => pFunc pa t <|> pFunc (pb ()) t)

instance {τ : Type u} : Monad (Parser τ) where
  bind x f := SafeParser.Intro (λt => pFunc x t >>= (λ(rx,r) => (λ(a,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (f rx) r))

instance {τ : Type u} : Bind (StrongParser τ) where
  bind x f := SafeParser.Intro (λt => pFunc x t >>= (λ(rx,r) => (λ(a,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (f rx) r))

class HSeqLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSeqLeft : α → (Unit → β) → γ

class HSeqRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSeqRight : α → (Unit → β) → γ

class HSeq (μ : Type u → Type v) (μ' : Type u → Type v') (μ'' : outParam (Type u → Type v'')) where
  hSeq {α : Type u} {β : Type u} : μ (α → β) → (Unit → μ' α) → μ'' β 

class HBind (μ : Type u → Type u') (μ' : Type u → Type v') (μ'' : outParam (Type u → Type v'')) where
  hBind {α : Type u} {β : Type u} : μ α → (α → μ' β) → μ'' β

notation a:arg "<<*" b:arg => HSeqLeft.hSeqLeft a (λ_ => b)
notation a:arg "*>>" b:arg => HSeqRight.hSeqRight a (λ_ => b)
notation a:arg "<**>" b:arg => HSeq.hSeq a b 
notation a:arg "*>>=" b:arg => HBind.hBind a b 

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqRight (Parser τ α) (Parser τ β) (Parser τ β) where
  hSeqRight p1 p2 := p1 >>= (λ_ => p2 ())

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqRight (StrongParser τ α) (Parser τ β) (StrongParser τ β) where
  hSeqRight p1 p2 :=
    SafeParser.Intro (λt => pFunc p1 t >>= (λ(_,r) => (λ(a,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (p2 ()) r))

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqRight (Parser τ α) (StrongParser τ β) (StrongParser τ β) where
  hSeqRight p1 p2 :=
    SafeParser.Intro (λt => pFunc p1 t >>= (λ(_,r) => (λ(a,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (p2 ()) r))

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqRight (StrongParser τ α) (StrongParser τ β) (StrongParser τ β) where
  hSeqRight p1 p2 :=
    SafeParser.Intro (λt => pFunc p1 t >>= (λ(_,r) => (λ(a,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (p2 ()) r))

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqLeft (Parser τ α) (Parser τ β) (Parser τ α) where
  hSeqLeft p1 p2 := p1 >>= (λr => p2 () >>= (λ_ => pure r))

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqLeft (StrongParser τ α) (Parser τ β) (StrongParser τ α) where
  hSeqLeft p1 p2 :=
    SafeParser.Intro (λt => pFunc p1 t >>= (λ(a,r) => (λ(_,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (p2 ()) r))

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqLeft (Parser τ α) (StrongParser τ β) (StrongParser τ α) where
  hSeqLeft p1 p2 :=
    SafeParser.Intro (λt => pFunc p1 t >>= (λ(a,r) => (λ(_,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (p2 ()) r))

instance {τ : Type u} {α : Type v} {β : Type v} : HSeqLeft (StrongParser τ α) (StrongParser τ β) (StrongParser τ α) where
  hSeqLeft p1 p2 :=
    SafeParser.Intro (λt => pFunc p1 t >>= (λ(a,r) => (λ(_,b) => (a,Subtype.mk b.val (by grind))) <$> pFunc (p2 ()) r))

instance {τ : Type u} : HSeq (Parser τ) (Parser τ) (Parser τ) where
  hSeq pf pa := Seq.seq pf pa

instance {τ : Type u} : HSeq (StrongParser τ) (Parser τ) (StrongParser τ) where
  hSeq pf pa := SafeParser.Intro (λt => pFunc pf t >>= (λ(f,r) => pFunc (pa ()) r >>= (λ(a,r') => pure (f a,Subtype.mk r'.val (by grind)))))

instance {τ : Type u} : HSeq (Parser τ) (StrongParser τ) (StrongParser τ) where
  hSeq pf pa := SafeParser.Intro (λt => pFunc pf t >>= (λ(f,r) => pFunc (pa ()) r >>= (λ(a,r') => pure (f a,Subtype.mk r'.val (by grind)))))

instance {τ : Type u} : HSeq (StrongParser τ) (StrongParser τ) (StrongParser τ) where
  hSeq pf pa := Seq.seq pf pa

instance {τ : Type u} : HBind (Parser τ) (Parser τ) (Parser τ) where
  hBind p f := p >>= f

instance {τ : Type u} : HBind (StrongParser τ) (Parser τ) (StrongParser τ) where
  hBind p f :=
    SafeParser.Intro (λt => pFunc p t >>= (λ(a,r) => pFunc (f a) r >>= (λ(b,r') => pure (b,Subtype.mk r'.val (by grind)))))

instance {τ : Type u} : HBind (Parser τ) (StrongParser τ) (StrongParser τ) where
  hBind p f :=
    SafeParser.Intro (λt => pFunc p t >>= (λ(a,r) => pFunc (f a) r >>= (λ(b,r') => pure (b,Subtype.mk r'.val (by grind)))))

instance {τ : Type u} : HBind (StrongParser τ) (StrongParser τ) (StrongParser τ) where
  hBind p f :=
    SafeParser.Intro (λt => pFunc p t >>= (λ(a,r) => pFunc (f a) r >>= (λ(b,r') => pure (b,Subtype.mk r'.val (by grind)))))

def char (c : Char) : StrongParser Char Char :=
  SafeParser.Intro (λt => match t with
    | [] => throw ("expected `" ++ String.ofList [c] ++ "` but got EOI!")
    | (x::xs) => if c = x then return (c,Subtype.mk xs (by grind))
      else
        throw ("expected `" ++ String.ofList [c] ++ "` but got " ++ String.ofList [x] ++ "!")
    )

def headProp {τ} [ToString τ] (prop : τ → Bool) : StrongParser τ τ :=
  SafeParser.Intro (λt => match t with
    | [] => throw ("expected head, got EOI!")
    | (x::xs) => if prop x then return (x,Subtype.mk xs (by grind))
      else
        throw ("head `" ++ toString x ++ "` does not conform to requested property!")
    )

def manyFunc {τ α} (p : StrongParser τ α) (t : List τ) : DCont String (List α × {tOut : List τ // tOut.length <= t.length}) :=
  DCont.Intro (λρ => λbf => λef => match pFunc p t with
    | DCont.Intro fpo =>
      fpo ρ (λc =>
        let bf' : List α × { tOut : List τ // tOut.length <= c.snd.val.length } → ρ := (λ(res,r) => bf (c.fst :: res,Subtype.mk r.val (by
          have Hc := c.snd.property
          have Hr := r.property
          grind
        )))
        run (manyFunc p c.2) ρ bf' (λ_ => bf ([c.fst],Subtype.mk c.snd (by grind)))) (λ_ => bf ([],Subtype.mk t (by grind))))
  termination_by t.length
  decreasing_by grind

def manyFuncP {τ α : Type u} (P : List τ → Prop) (H : ∀t, P t → forall t', t'.length <= t.length → P t') (p : (tIn : { tt : List τ // P tt }) → DCont String (α × {tOut : List τ // tOut.length < tIn.val.length}) ) (t : { tt : List τ // P tt }) : DCont String (List α × {tOut : List τ // tOut.length <= t.val.length}) :=
  DCont.Intro (λρ => λbf => λef => match p t with
    | DCont.Intro fpo =>
      fpo ρ (λc =>
        let bf' : List α × { tOut : List τ // tOut.length <= c.snd.val.length } → ρ := (λ(res,r) => bf (c.fst :: res,Subtype.mk r.val (by
          have Hc := c.snd.property
          have Hr := r.property
          grind
        )))
        run (manyFuncP P H p (Subtype.mk c.2.val (by grind))) ρ bf' (λ_ => bf ([c.fst],Subtype.mk c.snd (by grind)))) (λ_ => bf ([],Subtype.mk t (by grind))))
  termination_by t.val.length
  decreasing_by grind

def many {τ α} (p : StrongParser τ α) : Parser τ (List α) :=
  SafeParser.Intro (manyFunc p)

def someFunc {τ α} (p : StrongParser τ α) (t : List τ) : DCont String (List α × {tOut : List τ // tOut.length < t.length}) :=
  DCont.Intro (λρ => λbf => λef => match pFunc p t with
    | DCont.Intro fpo =>
      fpo ρ (λc =>
        let bf' : List α × { tOut : List τ // tOut.length < c.snd.val.length } → ρ := (λ(res,r) => bf (c.fst :: res,Subtype.mk r.val (by
          have Hc := c.snd.property
          have Hr := r.property
          grind
        )))
        run (someFunc p c.2) ρ bf' (λ_ => bf ([c.fst],Subtype.mk c.snd (by grind)))) ef)
  termination_by t.length
  decreasing_by grind

def some {τ α} (p : StrongParser τ α) : StrongParser τ (List α) :=
  SafeParser.Intro (someFunc p)

def eoi {τ} [ToString τ] : Parser τ Unit :=
  SafeParser.Intro (λt => match t with
    | [] => pure ((),Subtype.mk [] (by grind))
    | _ => throw ("expected EOI, but " ++ t.toString ++ " was left!")
  )

def digitChar : StrongParser Char Char := headProp (λc : Char => c.isDigit)

def digit : StrongParser Char Nat := (λc => (c.val - '0'.val).toNat) <$> digitChar 

def nat : StrongParser Char Nat := (List.foldl (λa b => a*10+b) 0) <$> some digit

def letter : StrongParser Char Char := headProp (λc : Char => c.isAlpha)

def identifier : StrongParser Char String := letter *>>= (λc => (λr => String.ofList (c :: r)) <$> many (letter <|> digitChar))

def parse {τ : Type u} {α : Type v} {P : List τ → List τ → Prop} (p : SafeParser τ P α) (ts : List τ) : String ⊕ α :=
  run (pFunc p ts) (String ⊕ α) (λ(a,_) => Sum.inr a) Sum.inl

def testParserSome : StrongParser Char String := String.ofList <$> ((_root_.some (char 'c' <|> char 't')) <<* (eoi : Parser Char Unit))

def testParserMany : Parser Char String := String.ofList <$> ((many (char 'c' <|> char 't')) <<* (eoi : Parser Char Unit))

def expressionFunc {τ α : Type u} [BEq τ] [ToString τ] (lp rp : τ) (atom : StrongParser τ α) (fullExprs exprs : List (StrongParser τ (α → α → α))) (H : exprs.length <= fullExprs.length) (t : List τ) : DCont String (α × {tOut : List τ // tOut.length < t.length}) := 
  DCont.Intro (λρ => λaf => λef => 
  match exprs with
  | [] => 
    match t with
    | [] => ef "Unexpected EOI!"
    | h :: r => if h == lp then
        run (expressionFunc lp rp atom fullExprs fullExprs (by grind) r) ρ (λ(ex,r) => match r with
          | Subtype.mk (h' :: r') H => if h' == rp then af (ex,Subtype.mk r' (by grind)) else ef ("Expected " ++ toString rp)
          | _ => ef ("Expected " ++ toString rp)
          ) ef
      else run (pFunc atom (h :: r)) ρ af ef
  | (e :: er) => 
    let pC := do
      let (lhs,rlhs) <- expressionFunc lp rp atom fullExprs er (by grind) t 
      let (tail,rrhs) <- manyFuncP (λt' => t'.length < t.length) (by grind) (λt' => do
        let (f,rf) <- pFunc e t'
        let (rhs, rff) <- expressionFunc lp rp atom fullExprs er (by grind) rf
        return ((f,rhs),Subtype.mk rff.val (by grind))
      ) rlhs
      return (List.foldl (λres (f,o) => f res o) lhs tail,Subtype.mk rrhs.val (by grind))
    let pO := expressionFunc lp rp atom fullExprs er (by grind) t 
    run (pC <|> pO) ρ af ef
    )
  termination_by (t.length * (fullExprs.length + 1) + exprs.length)
  decreasing_by
    all_goals simp_wf
    · grind 
    · have Hrft : rf.val.length < t.length := by grind
      have Hineq : ∀ a b c d, a < d → a * (b + 1) + c < d * (b + 1) + (c + 1) := by 
        intros a b c d Had
        induction b
        case zero =>
          grind
        case succ Hi n =>
          grind
      apply Hineq
      exact Hrft

def expression {τ α : Type u} [BEq τ] [ToString τ] (lp rp : τ) (atom : StrongParser τ α) (exprs : List (StrongParser τ (α → α → α))) : StrongParser τ α := 
  SafeParser.Intro (expressionFunc lp rp atom exprs exprs (by grind))

def sumEx.{u} : StrongParser Char Nat := expression '(' ')' nat.{u} [(λ_ => (· + ·)) <$> char.{u} '+']

def mathEx.{u} : StrongParser Char Nat := expression '(' ')' nat.{u} [(λc => if c == '+' then (· + ·) else (· - ·)) <$> (char.{u} '+' <|> char.{u} '-'),(λ_ => (· * ·)) <$> char.{u} '*']

#eval parse testParserMany "cctcctst".toList
#eval parse testParserMany "cctcctt".toList
#eval parse testParserMany "".toList
#eval parse testParserSome "cctcctst".toList
#eval parse testParserSome "cctcctt".toList
#eval parse testParserSome "".toList
#eval parse nat "12345".toList 
#eval parse identifier "a12345".toList 
#eval parse mathEx.{0} "10-(2+3+4)".toList 
