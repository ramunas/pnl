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
  (* permission set *)
  type pset

  type name_perm

  val swap : name * name -> name_perm
  val idPerm : name_perm
  val compose : name_perm -> name_perm -> name_perm

  val getNameSort : name -> name_sort
  val getVarSort : variable -> sort
  val getPSet : variable -> pset

  val var : string * sort * pset -> variable
  val name : string * name_sort -> name


  type sym

  val getSymName : sym -> string
  val getSymSort : sym -> sort * base_sort

  type term

  val nameTerm  : name -> term
  val varTerm   : variable -> term
  val tupleTerm : term list -> term
  val symTerm   : sym * term -> term
  val absTerm   : name * term -> term

  val applyNamePerm : name_perm -> term -> term


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


  datatype name
    = Name of string * name_sort

  val name = Name

  datatype pset
    = PSet of (name_sort list) * (name_sort list)

  datatype variable
    = Variable of string * sort * pset

  val var = Variable

  fun getNameSort (Name (_,s)) = s
  fun getVarSort (Variable (_,s,_)) = s
  fun getPSet (Variable (_,_,p)) = p


  datatype name_perm
    = NamePerm of name -> name

  val idPerm = NamePerm (fn n => n)

  fun swap (a, b) = 
    NamePerm (fn c =>
        if a = c then b
        else if b = c then a
        else c)

  fun compose (NamePerm p1) (NamePerm p2) =
    NamePerm (p1 o p2)


  datatype sym
    = Symbol of string * sort * base_sort

  fun getSymName (Symbol (name,_,_)) = name
  fun getSymSort (Symbol (_,sort,baseSort)) = (sort,baseSort)


  datatype term
    = NameTerm of name
    | VarTerm of variable
    | TupleTerm of term list
    | SymTerm of sym * term
    | AbsTerm of name * term


  val nameTerm  = NameTerm
  val varTerm   = VarTerm
  val tupleTerm = TupleTerm
  val symTerm   = SymTerm
  val absTerm   = AbsTerm

  fun applyNamePerm (NamePerm p) (NameTerm n) = NameTerm (p n)
    | applyNamePerm (NamePerm p) (VarTerm n) = Err.error "Perm on var term"
    | applyNamePerm (NamePerm p) (TupleTerm args) = TupleTerm (map (applyNamePerm (NamePerm p)) args)
    | applyNamePerm (NamePerm p) (SymTerm (sym,term)) = SymTerm (sym, applyNamePerm (NamePerm p) term)
    | applyNamePerm (NamePerm p) (AbsTerm (name, term)) =
    AbsTerm (p name, applyNamePerm (NamePerm p) term)

  (* fun inferType x = Err.error "" *)


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
    tok "namesort" >> ws () >> identifier () >>= return o NameSortSpec

  fun parseBaseSortDecl () =
    tok "sort" >> ws () >> identifier () >>= return o BaseSortSpec

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
    tok "sym" >> ws () >>
    identifier () >>= (fn id =>
    tok ":" >>
    delayed parseSort >>= (fn sort =>
    tok "=>" >> ws () >> identifier () >>= (fn bs =>
    return (SymSpec (Symbol (id, sort, bs)))
    )))


  fun parseSpec () =
    many (
            parseNameSortDecl ()
        </choice/>
            parseBaseSortDecl ()
        </choice/>
            parseSymDecl ()
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
         | LEFT (P.Error m, s) => Err.error m
         | RIGHT (r,s) => toSpecification r emptySpecification
    end)

  end (* end of local open *)

end;


PolyML.print_depth 100;
NomTerm.readSpecFromFile "test.spec";

