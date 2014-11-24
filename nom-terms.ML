(**
  uses lib/missing,
       lib/parser,
       lib/missing-io
  *)

signature NOM_TERM =
sig
  type base_sort
  type name_sort
  type sort

  val nameSort  : name_sort -> sort
  val baseSort  : base_sort -> sort
  val tupleSort : sort list -> sort
  val absSort   : name_sort * sort -> sort

  val sortToString : sort -> string

  type name
  type variable
  type pset

  val isLeft : name -> bool
  val isRight : name -> bool

  type name_perm

  val pSwap         : name * name -> name_perm
  val pId           : name_perm
  val pCompose      : name_perm -> name_perm -> name_perm
  val pApp          : name_perm -> name -> name
  val pIsWellSorted : name_perm -> (string, unit) Either.either

  val getNameSort : name -> name_sort
  val getVarSort : variable -> sort
  val getPSet : variable -> pset
  val pAppPSet : name_perm -> pset -> pset
  val makePSet : unit -> pset

  type name_pol
  val polLeft : name_pol
  val polRight : name_pol
  val makeVar : string * sort * pset -> variable
  val makeName : string * name_pol * name_sort -> name

  type sym

  val getSymName : sym -> string
  val getSymSort : sym -> sort * base_sort

  type term

  val nameTerm  : name -> term
  val varTerm   : variable -> term
  val tupleTerm : term list -> term
  val symTerm   : sym * term -> term
  val absTerm   : name * term -> term
  val pAppTerm : name_perm -> term -> term


  type nameset
  val fa : term -> nameset


  (* val inferType : term -> (string, sort * base_sort) Either.either *)
  (*
  val unify : term -> term ->
  *)


  (* type specification *)
  (* val emptySpecification : specification *)
  (* val readSpec : string -> specification *)
  (* val readSpecFromFile : string -> specification *)


  val test : unit -> unit

end;




structure NomTerm : NOM_TERM =
struct
  open Missing

  type base_sort = string
  type name_sort = string

  datatype sort
    = NameSort of name_sort
    | BaseSort of base_sort
    | TupleSort of sort list
    | AbsSort of name_sort * sort

  val nameSort = NameSort
  val baseSort = BaseSort
  val tupleSort = TupleSort
  val absSort = AbsSort

  fun join x (a::b::xs) = a ^ x ^ join x (b::xs)
    | join x (a::[]) = a
    | join x ([]) = ""

  fun sortToString (NameSort x) = x
    | sortToString (BaseSort x) = x
    | sortToString (TupleSort sorts) = "(" ^ (join ", " (map sortToString sorts)) ^ ")"
    | sortToString (AbsSort (nameSort, sort)) = "[" ^ nameSort ^ "]" ^ (sortToString sort)


  datatype name_pol = NameLeft | NameRight

  val polLeft = NameLeft
  val polRight = NameRight

  datatype name
    = Name of string * name_pol * name_sort

  val makeName = Name

  fun isLeft (Name (_,NameLeft,_)) = true
    | isLeft _ = false

  fun isRight (Name (_,NameRight,_)) = true
    | isRight _ = false

  fun getNameSort (Name (_,_,s)) = s

  datatype fin_name_perm =
    FinPerm of (name * name) list

  type name_perm = fin_name_perm

  val pId = FinPerm []
  fun pCompose (FinPerm p1) (FinPerm p2) = (FinPerm (p1 @ p2))
  fun pSwap (a,b) = FinPerm [(a,b)]
  fun pInverse (FinPerm p) = FinPerm (reverse p)

  fun swapName (a,b) c =
    if a = c then b
    else if b = c then a
    else c

  fun pApp (FinPerm p) n =
    List.foldr (fn (s, c) => swapName s c) n p

  fun nontriv (FinPerm p) =
    flatmap (fn (a,b) => [a,b]) p |>
    filter (fn a => not (a = pApp (FinPerm p) a))

  fun pIsWellSorted' [] = RIGHT ()
    | pIsWellSorted' ((a,b)::rest) =
    if getNameSort a = getNameSort b
        then pIsWellSorted' rest
        else LEFT "a and b is not well sorted"

  fun pIsWellSorted (FinPerm p) = pIsWellSorted' p

  datatype pset
    = PSet of (name list) * (name list)

  fun makePSet () = PSet ([],[])

  fun psetMember a (PSet (aset,bset)) =
    if isLeft a
        then not (Lst.member a aset)
        else member a bset

  fun psetSubset (PSet (aset1, bset1)) (PSet (aset2, bset2)) =
    all (fn b => member b bset2) bset1 andalso
    (all (fn a => member a aset1) aset2)

  fun remove a aset =
    filter (fn b => not(a = b)) aset

  fun psetAddName a (PSet (aset,bset)) =
    if isLeft a
        then PSet (remove a aset, bset)
        else PSet (aset, a::bset)

  fun psetRemName a (PSet (aset,bset)) =
    if isLeft a
        then (PSet (a::aset,bset))
        else (PSet (aset, remove a bset))

  fun psetUnion (PSet (aset1,bset1)) (PSet (aset2,bset2)) =
    PSet (intersection aset1 aset2, bset1 @ bset2)

  fun psetSwapName (a,b) pset =
    case (psetMember a pset, psetMember b pset) of
         (true,true)   => pset
       | (true,false)  => psetAddName b (psetRemName a pset)
       | (false,true)  => psetAddName a (psetAddName b pset)
       | (false,false) => pset

  fun psetAppPerm p pset =
    List.foldr (fn (p,ps) => psetSwapName p ps) pset p

  fun pAppPSet (FinPerm p) pset = psetAppPerm p pset


  datatype variable
    = Variable of string * sort * pset

  val makeVar = Variable
  fun getVarSort (Variable (_,s,_)) = s
  fun getPSet (Variable (_,_,p)) = p


  datatype sym
    = Symbol of string * sort * base_sort

  fun getSymName (Symbol (name,_,_)) = name
  fun getSymSort (Symbol (_,sort,baseSort)) = (sort,baseSort)


  datatype term
    = NameTerm of name
    | VarTerm of name_perm * variable
    | TupleTerm of term list
    | SymTerm of sym * term
    | AbsTerm of name * term

  val nameTerm  = NameTerm
  fun varTerm v = VarTerm (pId, v)
  val tupleTerm = TupleTerm
  val symTerm   = SymTerm
  val absTerm   = AbsTerm

  fun pAppTerm p (NameTerm n) = NameTerm (pApp p n)
    | pAppTerm p (VarTerm n) = Err.error "Perm on var term"
    | pAppTerm p (TupleTerm args) = TupleTerm (map (pAppTerm p) args)
    | pAppTerm p (SymTerm (sym,term)) = SymTerm (sym, pAppTerm p term)
    | pAppTerm p (AbsTerm (name, term)) = AbsTerm (pApp p name, pAppTerm p term)


  fun permShiftVarRemName a (Variable (n,s,p)) =
    VarTerm (pId, Variable (n,s,psetRemName a p))


  datatype nameset
    = FinNameSet of name list
    | PNameSet of pset


  fun nameSetUnion (FinNameSet aset) (FinNameSet bset) =
    FinNameSet (aset @ bset)
    | nameSetUnion (FinNameSet aset) (PNameSet pset) =
    PNameSet $ List.foldr (fn (a,ps) => psetAddName a ps) pset aset
    | nameSetUnion (PNameSet pset) (FinNameSet aset) =
    PNameSet $ List.foldr (fn (a,ps) => psetAddName a ps) pset aset
    | nameSetUnion (PNameSet pset1) (PNameSet pset2) =
    PNameSet $ psetUnion pset1 pset2

  fun nameSetMinus (FinNameSet aset) (FinNameSet bset) =
    FinNameSet $ minus aset bset
    | nameSetMinus (FinNameSet cset) (PNameSet (PSet (aset,bset))) =
    FinNameSet $
      filter (fn c => if isLeft c
                          then member c aset
                          else not (member c bset)) cset
    | nameSetMinus (PNameSet pset) (FinNameSet cset) =
        PNameSet $
            List.foldr (fn (c, ps) => psetRemName c ps) pset cset
    | nameSetMinus (PNameSet (PSet (aset1,bset1))) (PNameSet (PSet (aset2,bset2))) =
        PNameSet $ PSet (minus aset2 aset1, minus bset1 bset2)


  fun nameSetSubset (FinNameSet aset) (FinNameSet bset) =
    all (fn a => member a bset) aset
    | nameSetSubset (FinNameSet aset) (PNameSet pset) =
    all (fn a => psetMember a pset) aset
    | nameSetSubset (PNameSet pset) (FinNameSet aset) =
    false
    | nameSetSubset (PNameSet pset1) (PNameSet pset2) =
    psetSubset pset1 pset2


  fun newNameFor (Name (n,pol,s)) (FinNameSet names) =
    let
      val n' = Name (n^"'",pol,s)
    in
      if member n' names
          then newNameFor n' (FinNameSet names)
          else n'
    end
    | newNameFor (Name (n,pol,s)) (PNameSet (PSet (aset,bset))) =
        newNameFor (Name (n,NameRight,s)) (FinNameSet bset)


  fun fa (NameTerm n) = FinNameSet [n]
    | fa (VarTerm (p,Variable (_,_,pset))) = PNameSet (pAppPSet p pset)
    | fa (SymTerm (_,t)) = fa t
    | fa (AbsTerm (n,t)) = fa t
    | fa (TupleTerm tms) =
        List.foldr
            (fn (ns,bns) => nameSetUnion ns bns)
            (FinNameSet []) (map fa tms)

  fun memberNS name (FinNameSet names) = member name names
    | memberNS name (PNameSet pset) = psetMember name pset

  fun fresh name nameSet = not (memberNS name nameSet)

  fun fv (NameTerm n) = []
    | fv (VarTerm (_,v)) = [v]
    | fv (SymTerm (_,t)) = fv t
    | fv (AbsTerm (_,t)) = fv t
    | fv (TupleTerm tms) = flatmap fv tms

  fun subst sigma (NameTerm n) = NameTerm n
    | subst sigma (SymTerm (s,t)) = SymTerm (s, subst sigma t)
    | subst sigma (AbsTerm (a,t)) = AbsTerm (a, subst sigma t)
    | subst sigma (TupleTerm tms) = TupleTerm (map (subst sigma) tms)
    | subst sigma (VarTerm (pi,var)) =
        case List.find (fn (v,_) => v = var) sigma of
             SOME (_,t) => pAppTerm pi t
           | NONE => (VarTerm (pi,var))


  fun permAgreeOn (FinPerm p1) (FinPerm p2) pset =
  let
    fun pnames p = flatmap (fn (a,b) => [a,b]) p
    val names = pnames p1 @ pnames p2
    val n = filter (fn n => psetMember n pset) names
  in
    all (fn n => pApp (FinPerm p1) n = pApp (FinPerm p2) n) names
  end

  fun alphaEq (t1 as (AbsTerm (a,t))) (AbsTerm (b,t')) =
        fresh b (fa t1) andalso
        getNameSort a = getNameSort b andalso
        alphaEq (pAppTerm (pSwap (a,b)) t) t'
    | alphaEq (NameTerm a) (NameTerm b) = a = b
    | alphaEq (SymTerm (s1,t1)) (SymTerm (s2,t2)) =
        s1 = s2 andalso alphaEq t1 t2
    | alphaEq (TupleTerm t1) (TupleTerm t2) =
        length t1 = length t2 andalso
        all (uncurry alphaEq) (zip t1 t2)
    | alphaEq (VarTerm (p1,v1)) (VarTerm (p2,v2)) =
        v1 = v2 andalso permAgreeOn p1 p2 (getPSet v1)
    | alphaEq _ _ = false


  datatype unification_el
    = UnifEq of term * term
    | UnifFresh of name * term

  type unification_problem = unification_el list

  exception NoMatch

  val rules = [

    (* Rule =a *)
    fn (UnifEq (NameTerm a, NameTerm b)) =>
      if a = b then ([],[]) else raise NoMatch
        | _ => raise NoMatch ,

    (* Rule =f *)
    fn (UnifEq (SymTerm (f,t), SymTerm (g,t'))) =>
        if f = g then ([], [UnifEq (t,t')]) else raise NoMatch
        | _ => raise NoMatch ,

    (* Rule =() *)
    fn (UnifEq (TupleTerm t, TupleTerm t')) =>
        if length t = length t'
            then ([], (map UnifEq (zip t t')))
            else raise NoMatch
        | _ => raise NoMatch ,

    (* Rule =[] *)
    fn (UnifEq (AbsTerm (a,t), AbsTerm (b,t'))) =>
      let
        val c = newNameFor a (nameSetUnion (fa t) (fa t'))
        val tt = pAppTerm (pSwap (c,a)) t
        val tt' = pAppTerm (pSwap (c,b)) t'
      in
        ([], [UnifEq (tt,tt')])
      end
        | _ => raise NoMatch ,

    (* Rule =X *)
    fn (UnifEq (VarTerm (pi,x), VarTerm (pi',x'))) =>
      if x = x'
        then
          let
            fun intersect names ps =
              filter (fn a => psetMember a ps) names
            val p = pCompose (pInverse pi) pi'
            val names = nontriv p
            val ps = getPSet x
            val fnames = intersect names ps
            val freshness =
              map (fn n => UnifFresh (n,VarTerm (pId,x))) fnames
          in
            ([], freshness)
          end
        else raise NoMatch
        | _ => raise NoMatch ,

    (* Rule F *)
    fn (UnifEq (t, VarTerm (pi,x))) =>
    let
      val t' = pAppTerm (pInverse pi) t
      val s = nameSetMinus (fa t') (fa (VarTerm (pId, x)))
    in
      case s of
           FinNameSet [] => raise NoMatch
         | FinNameSet (a::_) =>
             ([], [UnifFresh (a, t'), UnifEq (t', VarTerm (pId,x))])
         | _ => error "This case should not occur unif"
    end
        | _ => raise NoMatch ,

    (* Rule F# *)
    fn (UnifFresh (a,t)) =>
      if fresh a (fa t) then ([],[]) else raise NoMatch
     | _ => raise NoMatch ,

    (* Rule Ff *)
    fn (UnifFresh (a, SymTerm (sym,t))) => ([], [UnifFresh (a,t)])
     | _ => raise NoMatch ,

    (* Rule F() *)
    fn (UnifFresh (a, TupleTerm tms)) =>
      ([], map (fn t => UnifFresh (a,t)) tms)
     | _ => raise NoMatch ,

    (* Rule F[] *)
    fn (UnifFresh (a, AbsTerm (b,t))) => ([], [UnifFresh (a,t)])
     | _ => raise NoMatch ,

    (* Rule IE *)
     (* pi here should be equiv to pId *)
    fn (UnifEq (t, VarTerm (pi,x))) =>
      if not (member x (fv t)) andalso
        nameSetSubset (fa t) (fa (VarTerm (pi,x)))
        then ([(x,t)], [])
        else raise NoMatch
     | _ => raise NoMatch ,

   fn (UnifFresh (a, VarTerm (pi,x))) =>
     ([(x, permShiftVarRemName a x)], [])
      | _ => raise NoMatch
  ]

  fun composeSubst s1 s2 = error ""

  fun applySubstPr subst = error ""

  fun uniRw subst [] = SOME subst
    | uniRw subst (pr::rest) =
    let
      fun applyRule [] = raise NoMatch
        | applyRule (r::rules) =
        case pr of
             UnifEq (t1,t2) => (r (UnifEq(t1,t2))
                                handle NoMatch =>
                                (r (UnifEq(t2,t1)) handle NoMatch =>
                                    applyRule rules))
          | _ => r pr handle NoMatch => applyRule rules
    in
      let
        val (subst',prs) = applyRule rules
        val s = composeSubst subst subst'
      in
        uniRw s (prs@(applySubstPr s rest))
      end
        handle NoMatch => NONE
    end


  fun unify t1 t2 = uniRw [] [UnifEq (t1, t2)]


  structure P = Parser(ParserStreamIO)
  local
    open Missing
    open P
  in

  fun readSpec _ = Err.error "Unimplemented"

  datatype name_modifier = AddNameToVar | RemNameToVar

  type ast_basesort = string
  type ast_namesort = string

  (* line, col, file *)
  type ast_pos = int * int * string

  datatype ast_abs_sort_kind
    = AstAbsSortSingle | AstAbsSortStar | AstAbsSortPlus

  datatype ast_sort
    = AstNameOrBaseSort of string
    | AstTupleSort of ast_sort list
    | AstAbsSort of ast_abs_sort_kind * string * ast_sort

  datatype ast_term
    = AstAbs of string * ast_term
    | AstVarTerm of ((string * string) list) * string
    | AstName of string
    | AstTuple of ast_term list
    | AstSym of string * (ast_term list)

  datatype ast_node
    = AstNameSortDecl of string
    | AstBaseSortDecl of string
    | AstNameDecl of string * name_pol * string
    | AstVarDecl of string * ((name_modifier * string) list)*ast_sort
    | AstSymDecl of string * ast_sort * ast_basesort
    | AstPredDecl of string * ast_sort
    | AstTermDecl of ast_term
    | AstRewriteDecl of ast_term * ast_term
    | AstSOSDecl of (ast_term * ast_term) list
    | AstRewriteStmtDecl of ast_term

  type ast = ast_node list

  fun notNl c = c <> #"\n"
  fun cmnt () =
    str "#" >>
    many ((sat notNl) </choice/> (eof () >> zero) ) >>
    (eof () </choice/> (item >> return ()))

  fun ws' () =
    ((sat Char.isSpace) >> return ()) </choice/> (cmnt ())
  fun ws () = many (ws' ())
  fun ws1 () = many1 (ws' ())


  fun identifier () =
    many1 (sat Char.isAlpha) >>= return o String.implode

  fun tok s = ws () >> str s >> return ()

  fun parseNameSortDecl () =
    tok "nametype" >> ws () >> nofail (identifier () >>= return o AstNameSortDecl)

  fun parseBaseSortDecl () =
    tok "type" >> ws () >> nofail (identifier () >>= return o AstBaseSortDecl)


  fun parseSort () =
        parseBaseOrNameSort ()
    </choice/>
        parseAbsSort ()
    </choice/>
        parseTupleSort ()
    </choice/>
        parseSortGroup ()

  and parseSortGroup () =
    tok "(" >>
    delayed parseSort >>= (fn s =>
    tok ")" >>
    return s)

  and parseBaseOrNameSort () =
    ws () >> identifier () >>= (fn r => return (AstNameOrBaseSort r))

  and parseAbsSortKind () =
        (tok "+" >> return AstAbsSortPlus)
    </choice/>
        (tok "*" >> return AstAbsSortStar)
    </choice/>
        (return AstAbsSortSingle)

  and parseAbsSort () =
    (tok "[" >>
    ws () >>
    identifier () >>= (fn r =>
    tok "]" >>
    parseAbsSortKind () >>= (fn k =>
    delayed parseSort >>= (fn s =>
    return (AstAbsSort (k,r,s)) ))))

  and parseTupleSort () =
    (tok "(" >> tok ")" >> return (AstTupleSort []))
        </choice/>
    (
        tok "(" >>
        (delayed parseSort) >>= (fn s =>
        tok "," >>
        ((delayed parseSort ) </sepby1/> (tok ",")) >>= (fn ss =>
        tok ")" >>
        return (AstTupleSort (s::ss))))
    )

  (* TODO: add mix-fix notation *)

  fun parseSymDecl () =
    tok "fn" >> ws1 () >>
    identifier () >>= (fn id =>
    tok ":" >>
    delayed parseSort >>= (fn sort =>
    tok "=>" >> ws () >> identifier () >>= (fn bs =>
    return (AstSymDecl (id, sort, bs))
    )))


  fun parseName () =
    identifier ()

  fun parseNameSort () = identifier ()

  fun parseNamePolSpec () =
    (str "<" >> return NameLeft)
    </choice/>
    (str ">" >> return NameRight)
    </choice/>
    (return NameLeft)

  fun parseNameDecl () =
    ws () >>
    str "name" >>
    ws1 () >>
    parseName () >>= (fn a =>
    ws () >>
    parseNamePolSpec () >>= (fn p =>
    ws () >>
    str ":" >>
    ws () >>
    parseNameSort () >>= (fn s =>
    return (AstNameDecl (a, p, s))
    )))



  fun parseVarNameMod () =
    (str "-" >> return RemNameToVar)
    </choice/>
    (str "+" >> return AddNameToVar)

  fun parseVarName () =
    ws () >>
    parseVarNameMod () >>= (fn m =>
    ws () >>
    parseName () >>= (fn a =>
    return (m,a)
    ))

  fun parseVarNames () =
    many (parseVarName ())

  fun parseVarDecl () =
    ws () >>
    str "var" >>
    nofail (
    ws1 () >>
    str "`" >>
    parseName () >>= (fn varName =>
    ws () >>
    parseVarNames () >>= (fn varContext =>
    ws () >>
    str ":" >>
    parseSort () >>= (fn varSort =>
    return (AstVarDecl (varName, varContext, varSort))
    ))))


  fun maybe p r = p </choice/> return r


  fun parseSwaps () =
    many (
    ws () >>
    str "(" >>
    parseName () >>= (fn a =>
    ws1 () >>
    parseName () >>= (fn b =>
    ws () >>
    str ")" >>
    return (a,b) )) )

  fun parseTerm () =
        parseTupleTerm ()
    </choice/>
        parseTermGroup ()
    </choice/>
        parseVarTerm ()
    </choice/>
        parseSymTerm ()
    </choice/>
        parseNameTerm ()
    </choice/>
        parseAbsTerm ()

  and parseSymTerm () =
    ws () >>
    identifier () >>= (fn i =>
    ws () >> str "(" >> nofail (ws () >>
    (parseTerm () </sepby/> (ws () >> str "," >> ws ())) >>= (fn tms =>
    ws () >> str ")" >>
    return (AstSym (i, tms))
    )))

  and parseAbsTerm () =
    ws () >> str "[" >> ws () >>
    parseName () >>= (fn x =>
    ws () >> str "]" >> ws () >>
    parseTerm () >>= (fn t =>
    return (AstAbs (x,t)) ))

  and parseTermGroup () =
    ws () >> str "(" >> delayed parseTerm >>= (fn t =>
    ws () >> str ")" >> return t)

  and parseUnitTupleTerm () =
    tok "(" >> tok ")" >> return (AstTuple [])

  and parseTupleTerm () =
        (parseUnitTupleTerm ())
    </choice/>
        (ws () >> str "(" >>
        delayed parseTerm >>= (fn t1 =>
        ws () >> str "," >> ws () >>
        ((ws () >> delayed parseTerm) </sepby1/> (ws () >> str ",")) >>= (fn tms =>
        ws () >> str ")" >>
        return (AstTuple (t1::tms)))))

  and parseVarTerm () =
    ws () >> str "`" >>
    parseSwaps () >>= (fn sw =>
    ws () >>
    identifier () >>= (fn name =>
    return (AstVarTerm (sw, name))
    ))

  and parseNameTerm () =
    identifier () >>= return o AstName

  fun parseTermDecl () =
    ws () >> str "term" >> ws1 () >>
    nofail (parseTerm () >>= return o AstTermDecl)

  fun parseRewriteDecl () =
    ws () >>
    str "rw" >>
    ws1 () >> nofail (
    parseTerm () >>= (fn t1 =>
    ws () >> str "==>" >> ws () >>
    parseTerm () >>= (fn t2 =>
    return (AstRewriteDecl (t1, t2))
    )))


  fun parseRewriteStatementDecl () =
    ws () >>
    str "rewrite" >>
    ws1 () >> nofail (
    parseTerm () >>= (fn t => return (PolyML.print (AstRewriteStmtDecl t))))


  fun parseSOSDecl () =
    ws () >>
    str "sos" >>
    ((parseTerm () >>= (fn t1 =>
    ws () >> str "-->" >>
    parseTerm () >>= (fn t2 =>
    return (t1,t2) )) ) </sepby1/> (ws () >> str "==>")) >>= (fn sos =>
    return (AstSOSDecl sos) )

  fun parseSpec () =
    many (
            parseNameSortDecl ()
        </choice/>
            parseBaseSortDecl ()
        </choice/>
            parseSymDecl ()
        </choice/>
            parseNameDecl ()
        </choice/>
            parseVarDecl ()
        </choice/>
            parseTermDecl ()
        </choice/>
            parseRewriteDecl ()
        </choice/>
            parseRewriteStatementDecl ()
        </choice/>
            parseSOSDecl ()
    ) >>= (fn r => ws () >> eof r)


  fun readSpecFromFile fileName =
    MissingIO.withOpenFile fileName (fn inStream =>
    let
      val ps = ParserStreamIO.make inStream
    in
      case parse (parseSpec ()) ps of
           LEFT (msg as (P.Fail m,s)) => Err.error (errormsg msg)
         | LEFT (msg as (P.Error m, s)) => Err.error (errormsg msg)
         | RIGHT (r,s) => r
    end)

  end (* end of local open *)

  datatype rewrite_rule
    = RewriteRule of term * term

  datatype sos_rule
    = SOSRule of string (* predicate list * *)

  datatype spec_node
    = SpecNameSort of name_sort
    | SpecBaseSort of base_sort
    | SpecName of name
    | SpecVar of variable
    | SpecSym of sym
    (* | SpecPred of predicate *)
    | SpecTerm of term
    | SpecRewrite of rewrite_rule
    | SpecRewriteStmt of term
    | SpecSOS of sos_rule

  type spec = spec_node list

  val emptyCont = []

  fun specNameSorts spec =
    spec |>
    filter (fn (SpecNameSort s) => true | _ => false) |>
    map (fn (SpecNameSort s) => s | _ => error "")

  fun specBaseSorts spec =
    spec |>
    filter (fn (SpecBaseSort s) => true | _ => false) |>
    map (fn (SpecBaseSort s) => s | _ => error "")


  exception CheckError of string
  fun err msg = raise CheckError msg

  fun fmt' ([], _) = []
    | fmt' (fmts, []) = fmts
    | fmt' (f::fmts, v::vals) =
    if f = "$"
        then v::(fmt' (fmts, vals))
        else f::(fmt' (fmts, v::vals))

  fun fmt fm vals =
    String.concat $
        fmt' (map Char.toString (String.explode fm), vals)

  fun ferr fm vals =
    err $ fmt fm vals

  fun checkNameSort spec sort =
    (case List.find (fn (SpecNameSort s) => s = sort
                     | _ => false) spec of
        SOME _ => sort
      | NONE => ferr "The sort $ hase not been declared." [sort])

  fun checkBaseSort spec sort =
    (case List.find (fn (SpecBaseSort s) => s = sort
                     | _ => false) spec of
        SOME _ => sort
      | NONE => ferr "The sort $ hase not been declared." [sort])

  fun checkAstSortToSort spec (AstNameOrBaseSort x) =
    (nameSort (checkNameSort spec x)
    handle (CheckError msg) =>
    (baseSort (checkBaseSort spec x)))

    | checkAstSortToSort spec (AstTupleSort sorts) =
        tupleSort (map (checkAstSortToSort spec) sorts)
    | checkAstSortToSort spec (AstAbsSort (AstAbsSortSingle,nameSort,sort)) =
        absSort (checkNameSort spec nameSort, checkAstSortToSort spec sort)
    | checkAstSortToSort spec _ = error "checkAstSortToSort"

  fun checkName spec name =
    case List.find (fn (SpecName (Name (n, p, s))) => n = name
                     | _ => false) spec of
         SOME (SpecName n) => n
       | NONE => ferr "The name $ has not been declared." [name]
       | _ => error "Uhandled case in checkName"

  fun checkVar spec name =
    case List.find (fn (SpecVar (Variable (n,_,_))) => name = n
                     | _ => false) spec of
         SOME (SpecVar (v)) => v
       | NONE => ferr "The variable '$' has not been declared." [name]
       | _ => error "checkVar"

  fun checkSym spec name =
    case List.find (fn (SpecSym (Symbol (n,_,_))) => name = n
                     | _ => false) spec of
         SOME (SpecSym (s)) => s
       | NONE => ferr "The symbol '$' has not been declared." [name]
       | _ => error "checkSym"

  fun checkAstPermToPerm spec astPerm =
    FinPerm $
        map (fn (a,b) => (checkName spec a, checkName spec b)) astPerm


  fun sortToString (NameSort n) = n
    | sortToString (BaseSort n) = n
    | sortToString (TupleSort tms) =
    "("^(join ", " (map sortToString tms))^")"
    | sortToString (AbsSort (n,s)) =
    fmt "[$]$" [n, sortToString s]

  fun typeCheck spec (NameTerm (Name (n,_,s))) (NameSort sort) =
    if s = sort
        then ()
        else ferr "The name '$' is expected to have the type '$' but '$' was found." [n,sort,s]
    | typeCheck spec (VarTerm (perm, Variable (n,s,ps))) sort =
    if s = sort
        then ()
        else ferr "The variable '$' is expected to have the type '$' but it has '$'" [n, sortToString sort, sortToString s]
    | typeCheck spec (TupleTerm tms) (TupleSort sorts) =
    if length tms = length sorts
        then forall (fn (t,s) => typeCheck spec t s) (zip tms sorts)
        else ferr "Tupleterm mismatch" []
    | typeCheck spec (AbsTerm (Name (n,_,s), tm)) (AbsSort (ns,sort)) =
    if s = ns
        then typeCheck spec tm sort
        else ferr "The name $ has the sort $ but $ was expected."
             [n, s, ns]
    | typeCheck spec (SymTerm (Symbol (n, s, b), tm)) (BaseSort sort) =
        if sort = b
            then typeCheck spec tm s
            else ferr "The symbol $ has the return type of $ but $ was expected" [n, b, sort]
    | typeCheck spec tm st =
        ferr "The term '$'(TODO) is expected to have the sort '$', but inferred '$'."
            ["", sortToString st, sortToString $ inferSort spec tm]


  and inferSort spec (NameTerm (Name (_,_,s))) = NameSort s
    | inferSort spec (VarTerm (perm, Variable (n,s,ps))) = s
    | inferSort spec (TupleTerm tms) =
        TupleSort (map (inferSort spec) tms)
    | inferSort spec (AbsTerm (Name (_,_,s), tm)) =
        AbsSort (s, inferSort spec tm)
    | inferSort spec (SymTerm (Symbol (n, s, b), tm)) =
    let
      val () = typeCheck spec tm s
    in
      BaseSort b
    end


  fun checkAstTermToTerm spec (AstName x) =
     NameTerm (checkName spec x)
    | checkAstTermToTerm spec (AstAbs (x, astTerm)) =
    AbsTerm (checkName spec x, checkAstTermToTerm spec astTerm)
    | checkAstTermToTerm spec (AstVarTerm (astPerm, varName)) =
    VarTerm (checkAstPermToPerm spec astPerm,
             checkVar spec varName)
    | checkAstTermToTerm spec (AstTuple astTerms) =
    TupleTerm (map (checkAstTermToTerm spec) astTerms)
    | checkAstTermToTerm spec (AstSym (name, tmsAst)) =
    let
      val sym = checkSym spec name
      val Symbol (_,_,bs) = sym
      val t = case tmsAst of
                   [] => SymTerm (sym, TupleTerm [])
                 | [astT] => SymTerm (sym, checkAstTermToTerm spec astT)
                 | astTerms => SymTerm (sym, TupleTerm (map (checkAstTermToTerm spec) astTerms))
      val _ = typeCheck spec t (BaseSort bs)
    in
      t
    end

  (*
   * TODO:
   * report erors in file positions
   *)
  fun astNodeToSpecNode (AstNameSortDecl s) spec =
    (case (List.find (fn (SpecNameSort a) => (s = a)
                      | (SpecBaseSort b) => (s = b)
                      | _ => false) spec) of
         SOME _ => ferr "The sort $ has been already declared" [s]
       | NONE => (SpecNameSort s))
    | astNodeToSpecNode (AstBaseSortDecl s) spec =
    (case (List.find (fn (SpecNameSort a) => (s = a)
                      | (SpecBaseSort b) => (s = b)
                      | _ => false) spec) of
         SOME _ => ferr "The sort $ has been already declared" [s]
       | NONE => (SpecBaseSort s))
    | astNodeToSpecNode (AstNameDecl (name,pol,sort)) spec =
      (case (List.find (fn (SpecNameSort s) => s = sort
                                 | _ => false) spec) of
            SOME _ => SpecName (Name (name, pol, sort))
          | NONE => ferr "The sort $ is not a name sort or it has not been declared." [sort]
      )

    | astNodeToSpecNode (AstVarDecl (name, n, sort)) spec =
    let
      val p = List.foldr (fn ((m,nn), ps) =>
            case m of
                 AddNameToVar => psetAddName (checkName spec nn) ps
               | RemNameToVar => psetRemName (checkName spec nn) ps
        ) (makePSet ()) n
      val s = checkAstSortToSort spec sort
      val v = makeVar (name, s, p)
    in
      SpecVar v
    end
    | astNodeToSpecNode (AstSymDecl (name, sort, baseSort)) spec =
    SpecSym $
        Symbol (name,
                checkAstSortToSort spec sort,
                checkBaseSort spec baseSort)
    | astNodeToSpecNode (AstTermDecl t) spec =
    let
      val tm = checkAstTermToTerm spec t
      val s = inferSort spec tm
    in
      case s of
           BaseSort _ => SpecTerm tm
         | _ => ferr "A term must have a base type, but found $."
                     [sortToString s]
    end
    | astNodeToSpecNode (AstRewriteDecl (astS, astT)) spec =
    let
      val s = checkAstTermToTerm spec astS
      val t = checkAstTermToTerm spec astT
      val sortA = inferSort spec s
      val sortB = inferSort spec t
    in
      if sortA = sortB
      (* TODO: there must be more checks, the names and vars of left
       * handside should be included on the right hand side *)
        then SpecRewrite $ RewriteRule (s,t)
        else ferr "Sort mismatch in a rewrite rule: '$' does not match '$'" [sortToString sortA, sortToString sortB]
    end

    | astNodeToSpecNode (AstRewriteStmtDecl ast) spec =
        SpecRewriteStmt (checkAstTermToTerm spec ast)

    | astNodeToSpecNode _ _ = SpecNameSort ""
    (*
    | astNodeToSpecNode (AstPredDecl s) spec = error "AstPredDecl"
    | astNodeToSpecNode (AstSOSDecl s) spec = error "AstSOSDecl"
    *)

  fun astToSpec' [] spec = spec
    | astToSpec' (astNode::ast) spec =
    astToSpec' ast
        (spec @ [(astNodeToSpecNode astNode spec)])

  fun astToSpec ast = astToSpec' ast []

  fun test () =
  let
    (* val file = "test.pnl" *)
    val file = "lam.pnl"
    val ast = readSpecFromFile file
    val spec = astToSpec ast
    val _ = PolyML.print ast
    val _ = PolyML.print spec
  in
    ()
  end

end;


PolyML.print_depth 100;
(* NomTerm.readSpecFromFile "test.spec"; *)
NomTerm.test ();

