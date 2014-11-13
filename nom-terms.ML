(**
  uses pwb/missing, pwb/parser, pwb/missing-io
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


  type specification

  val emptySpecification : specification

  val readSpec : string -> specification
  val readSpecFromFile : string -> specification

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

  fun swapName (a,b) c =
    if a = c then b
    else if b = c then a
    else c

  fun pApp (FinPerm p) n =
    List.foldr (fn (s, c) => swapName s c) n p

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

  datatype nameset
    = FinNameSet of name list
    | PNameSet of pset

  (* fun nsUnion  *)

  fun fa (NameTerm n) = FinNameSet [n]
    | fa (VarTerm (p, Variable (_,_,pset))) = PNameSet (pAppPSet p pset)
    | fa (SymTerm (_,t)) = fa t
    | fa (AbsTerm (n,t)) = fa t
    | fa (TupleTerm tms) = Err.error "unimplemented tms"



  datatype specification
    = Spec of name_sort list * base_sort list * sym list

  val emptySpecification = []

  fun getNameSorts (Spec (s,_,_)) = s
  fun getBaseSorts (Spec (_,b,_)) = b
  fun getSymList   (Spec (_,_,s)) = s


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
    | AstVarDecl of string * ((name_modifier * string) list) * ast_sort
    | AstSymDecl of string * ast_sort * ast_basesort
    | AstTermDecl of ast_term

  type ast = ast_node list
  type specification = ast

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

  fun parseSymDecl () =
    tok "symbol" >> ws1 () >>
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

  (* TODO: add mixfix
   * to resolve this, one would like to have a sym list,
   * and a var list *)
  and parseSymTerm () =
    ws () >>
    identifier () >>= (fn i =>
    ws () >> str "(" >> ws () >>
    (parseTerm () </sepby/> (ws () >> str ",")) >>= (fn tms =>
    ws () >> str ")" >>
    return (AstSym (i, tms))
    ))

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
    ) >>= (fn r => ws () >> eof r)


  fun readSpecFromFile fileName =
    MissingIO.withOpenFile fileName (fn inStream =>
    let
      val ps = ParserStreamIO.make inStream
    in
      case parse (parseSpec ()) ps of
           LEFT (P.Fail m,s) => Err.error m
         | LEFT (msg as (P.Error m, s)) => Err.error (errormsg msg)
         | RIGHT (r,s) => r
    end)

  end (* end of local open *)

end;


PolyML.print_depth 100;
NomTerm.readSpecFromFile "test.spec";

