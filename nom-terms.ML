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
  fun pSwap (a,b) = Err.error ""

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

  val emptySpecification = Spec ([],[],[])

  fun getNameSorts (Spec (s,_,_)) = s
  fun getBaseSorts (Spec (_,b,_)) = b
  fun getSymList   (Spec (_,_,s)) = s


  structure P = Parser(ParserStreamIO)
  local
    open Missing
    open P
  in

  fun readSpec _ = Err.error "Unimplemented"

  datatype spec'
    = NameSortSpec of name_sort
    | BaseSortSpec of base_sort
    | SymSpec of sym

  type spec = spec' list

  fun notNl c = c <> #"\n"
  fun cmnt () =
    str "#" >>
    many ((sat notNl) </choice/> (eof () >> zero) ) >>
    (eof () </choice/> (item >> return ()))

  (* fun ws () = many (sat Char.isSpace) *)
  fun ws () =
    many (((sat Char.isSpace) >> return ()) </choice/> (cmnt ()))


  fun identifier () =
    many1 (sat Char.isAlpha) >>= return o String.implode

  fun tok s = ws () >> str s >> return ()

  fun parseNameSortDecl () =
    tok "namesort" >> ws () >> nofail (identifier () >>= return o NameSortSpec)

  fun parseBaseSortDecl () =
    tok "sort" >> ws () >> nofail (identifier () >>= return o BaseSortSpec)

  fun parseSort () =
      (tok "[" >> ws () >> identifier () >>= (fn r => tok "]" >>
      delayed parseSort >>= (fn s =>
      return (AbsSort (r,s)) )) )
    </choice/>
        (tok "(" >> delayed parseSort </sepby/> (tok ",") >>=
        (fn r => tok ")" >> return (TupleSort r)))
    </choice/>
        (* Do I need to distinguish between name and base sorts? *)
        (ws () >> identifier () >>= (fn r => return (BaseSort r)))

  fun parseSymDecl () =
    tok "symbol" >> ws () >>
    identifier () >>= (fn id =>
    tok ":" >>
    delayed parseSort >>= (fn sort =>
    tok "=>" >> ws () >> identifier () >>= (fn bs =>
    return (SymSpec (Symbol (id, sort, bs)))
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

  fun parseNameDef () =
    ws () >> 
    parseName () >>= (fn a =>
    ws () >>
    parseNamePolSpec () >>= (fn p =>
    str ":" >>
    parseNameSort () >>= (fn s =>
    return (Name (a, p, s))
    )))

  fun parseSpec () =
    many (
            parseNameSortDecl ()
        </choice/>
            parseBaseSortDecl ()
        </choice/>
            parseSymDecl ()
        </choice/>
            (ws () >> str "name" >> ws () >> parseNameDef () >> return (NameSortSpec "here"))
    ) >>= (fn r => ws () >> eof r)

  fun toSpecification [] r = r
    | toSpecification ((NameSortSpec s)::rest) (Spec (ns,bs,ss)) =
    toSpecification rest (Spec (s::ns,bs,ss))
    | toSpecification ((BaseSortSpec b)::rest) (Spec (ns,bs,ss)) =
    toSpecification rest (Spec (ns, b::bs,ss))
    | toSpecification ((SymSpec s)::rest) (Spec (ns,bs,ss)) =
    toSpecification rest (Spec (ns,bs,s::ss))


  fun readSpecFromFile fileName =
    MissingIO.withOpenFile fileName (fn inStream =>
    let
      val ps = ParserStreamIO.make inStream
    in
      case parse (parseSpec ()) ps of
           LEFT (P.Fail m,s) => Err.error m
         | LEFT (msg as (P.Error m, s)) => Err.error (errormsg msg)
         | RIGHT (r,s) => toSpecification r emptySpecification
    end)

  end (* end of local open *)

end;


PolyML.print_depth 100;
NomTerm.readSpecFromFile "test.spec";

