structure MD5 (* :> MD5 *) =
struct
  exception Unimplemented

  val xorb    = Word32.xorb
  val andb    = Word32.andb
  val orb     = Word32.orb
  val shiftlb = Word32.<<
  val shiftrb = Word32.>>
  val notb    = Word32.notb

  type w32 = word
  infix xorb andb orb shiftlb shiftrb

  (* workaround for andb bug in MLton 20010706 *)
  fun mkbyte w = Word32.mod (w, 0w256)

  fun F(X,Y,Z) = (X andb Y) orb (notb X andb Z)
  fun G(X,Y,Z) = (X andb Z) orb (Y andb notb Z)
  fun H(X,Y,Z) = X xorb Y xorb Z
  fun I(X,Y,Z) = Y xorb (X orb notb Z)

  fun ROL(X, N) = (X shiftlb N) orb (X shiftrb (0w32-N))

  fun wc hi lo = (hi shiftlb 0w16) orb lo

  fun w2b w = map chr 
    [Word32.toInt (mkbyte w),
     Word32.toInt (mkbyte (w shiftrb 0w8)),
     Word32.toInt (mkbyte (w shiftrb 0w16)),
     Word32.toInt (mkbyte (w shiftrb 0w24))]

  (* pad a message (in the prescribed manner) to be congruent to
     56 bytes (mod 64) *)
  fun pad m l =
    let val v = l mod 64
        val p = if v < 56 then 56 - v else 120 - v
    in m ^ (str (chr 0x80)) ^
       implode (List.tabulate (p - 1, fn _ => chr 0))
    end

  (* append the length as a 64-bit quantity. *)
  fun applen m l =
    m ^
    implode (w2b (Word32.fromInt (l * 8))) ^
    implode (List.tabulate (4, fn _ => chr 0))

  fun FF (a, b, c, d, x, s, ac) =
    ROL(a + F(b, c, d) + x + ac, s) + b

  fun GG (a, b, c, d, x, s, ac) =
    ROL(a + G(b, c, d) + x + ac, s) + b

  fun HH (a, b, c, d, x, s, ac) =
    ROL(a + H(b, c, d) + x + ac, s) + b

  fun II (a, b, c, d, x, s, ac) =
    ROL(a + I(b, c, d) + x + ac, s) + b

  fun doblock (aa,bb,cc,dd) x =
    let
      (* get the nth logical byte from the input block *)
      val a = aa
      val b = bb
      val c = cc
      val d = dd

      val a = FF (a, b, c, d, x  0, 0w7,  wc 0wxd76a 0wxa478)
      val d = FF (d, a, b, c, x  1, 0w12, wc 0wxe8c7 0wxb756)
      val c = FF (c, d, a, b, x  2, 0w17, wc 0wx2420 0wx70db)
      val b = FF (b, c, d, a, x  3, 0w22, wc 0wxc1bd 0wxceee)
      val a = FF (a, b, c, d, x  4, 0w7,  wc 0wxf57c 0wx0faf)
      val d = FF (d, a, b, c, x  5, 0w12, wc 0wx4787 0wxc62a)
      val c = FF (c, d, a, b, x  6, 0w17, wc 0wxa830 0wx4613)
      val b = FF (b, c, d, a, x  7, 0w22, wc 0wxfd46 0wx9501)
      val a = FF (a, b, c, d, x  8, 0w7,  wc 0wx6980 0wx98d8)
      val d = FF (d, a, b, c, x  9, 0w12, wc 0wx8b44 0wxf7af)
      val c = FF (c, d, a, b, x 10, 0w17, wc 0wxffff 0wx5bb1)
      val b = FF (b, c, d, a, x 11, 0w22, wc 0wx895c 0wxd7be)
      val a = FF (a, b, c, d, x 12, 0w7,  wc 0wx6b90 0wx1122)
      val d = FF (d, a, b, c, x 13, 0w12, wc 0wxfd98 0wx7193)
      val c = FF (c, d, a, b, x 14, 0w17, wc 0wxa679 0wx438e)
      val b = FF (b, c, d, a, x 15, 0w22, wc 0wx49b4 0wx0821)


      val a = GG (a, b, c, d, x  1, 0w5,  wc 0wxf61e 0wx2562)
      val d = GG (d, a, b, c, x  6, 0w9,  wc 0wxc040 0wxb340)
      val c = GG (c, d, a, b, x 11, 0w14, wc 0wx265e 0wx5a51)
      val b = GG (b, c, d, a, x  0, 0w20, wc 0wxe9b6 0wxc7aa)
      val a = GG (a, b, c, d, x  5, 0w5,  wc 0wxd62f 0wx105d)
      val d = GG (d, a, b, c, x 10, 0w9,  wc 0wx0244 0wx1453)
      val c = GG (c, d, a, b, x 15, 0w14, wc 0wxd8a1 0wxe681)
      val b = GG (b, c, d, a, x  4, 0w20, wc 0wxe7d3 0wxfbc8)
      val a = GG (a, b, c, d, x  9, 0w5,  wc 0wx21e1 0wxcde6)
      val d = GG (d, a, b, c, x 14, 0w9,  wc 0wxc337 0wx07d6)
      val c = GG (c, d, a, b, x  3, 0w14, wc 0wxf4d5 0wx0d87)
      val b = GG (b, c, d, a, x  8, 0w20, wc 0wx455a 0wx14ed)
      val a = GG (a, b, c, d, x 13, 0w5,  wc 0wxa9e3 0wxe905)
      val d = GG (d, a, b, c, x  2, 0w9,  wc 0wxfcef 0wxa3f8)
      val c = GG (c, d, a, b, x  7, 0w14, wc 0wx676f 0wx02d9)
      val b = GG (b, c, d, a, x 12, 0w20, wc 0wx8d2a 0wx4c8a)

      val a = HH (a, b, c, d, x  5, 0w4,  wc 0wxfffa 0wx3942)
      val d = HH (d, a, b, c, x  8, 0w11, wc 0wx8771 0wxf681)
      val c = HH (c, d, a, b, x 11, 0w16, wc 0wx6d9d 0wx6122)
      val b = HH (b, c, d, a, x 14, 0w23, wc 0wxfde5 0wx380c)
      val a = HH (a, b, c, d, x  1, 0w4,  wc 0wxa4be 0wxea44)
      val d = HH (d, a, b, c, x  4, 0w11, wc 0wx4bde 0wxcfa9)
      val c = HH (c, d, a, b, x  7, 0w16, wc 0wxf6bb 0wx4b60)
      val b = HH (b, c, d, a, x 10, 0w23, wc 0wxbebf 0wxbc70)
      val a = HH (a, b, c, d, x 13, 0w4,  wc 0wx289b 0wx7ec6)
      val d = HH (d, a, b, c, x  0, 0w11, wc 0wxeaa1 0wx27fa)
      val c = HH (c, d, a, b, x  3, 0w16, wc 0wxd4ef 0wx3085)
      val b = HH (b, c, d, a, x  6, 0w23, wc 0wx0488 0wx1d05)
      val a = HH (a, b, c, d, x  9, 0w4,  wc 0wxd9d4 0wxd039)
      val d = HH (d, a, b, c, x 12, 0w11, wc 0wxe6db 0wx99e5)
      val c = HH (c, d, a, b, x 15, 0w16, wc 0wx1fa2 0wx7cf8)
      val b = HH (b, c, d, a, x  2, 0w23, wc 0wxc4ac 0wx5665)

      val a = II (a, b, c, d, x  0, 0w6,  wc 0wxf429 0wx2244)
      val d = II (d, a, b, c, x  7, 0w10, wc 0wx432a 0wxff97)
      val c = II (c, d, a, b, x 14, 0w15, wc 0wxab94 0wx23a7)
      val b = II (b, c, d, a, x  5, 0w21, wc 0wxfc93 0wxa039)
      val a = II (a, b, c, d, x 12, 0w6,  wc 0wx655b 0wx59c3)
      val d = II (d, a, b, c, x  3, 0w10, wc 0wx8f0c 0wxcc92)
      val c = II (c, d, a, b, x 10, 0w15, wc 0wxffef 0wxf47d)
      val b = II (b, c, d, a, x  1, 0w21, wc 0wx8584 0wx5dd1)
      val a = II (a, b, c, d, x  8, 0w6,  wc 0wx6fa8 0wx7e4f)
      val d = II (d, a, b, c, x 15, 0w10, wc 0wxfe2c 0wxe6e0)
      val c = II (c, d, a, b, x  6, 0w15, wc 0wxa301 0wx4314)
      val b = II (b, c, d, a, x 13, 0w21, wc 0wx4e08 0wx11a1)
      val a = II (a, b, c, d, x  4, 0w6,  wc 0wxf753 0wx7e82)
      val d = II (d, a, b, c, x 11, 0w10, wc 0wxbd3a 0wxf235)
      val c = II (c, d, a, b, x  2, 0w15, wc 0wx2ad7 0wxd2bb)
      val b = II (b, c, d, a, x  9, 0w21, wc 0wxeb86 0wxd391)
    in
      (a + aa, b + bb, c + cc, d + dd)
    end

  fun b2w (a, b, c, d) =
    (Word32.fromInt (ord a)) +
    (Word32.fromInt (ord b) shiftlb 0w8)  +
    (Word32.fromInt (ord c) shiftlb 0w16) +
    (Word32.fromInt (ord d) shiftlb 0w24)   

  fun md5_advanced {len, msg} =
    let
      val m = pad msg len
      val m = applen m len

      val len = size m

      val (a,b,c,d) = (wc 0wx6745 0wx2301,
                       wc 0wxefcd 0wxab89,
                       wc 0wx98ba 0wxdcfe,
                       wc 0wx1032 0wx5476)

      fun mkx off x =
        b2w (CharVector.sub (m, off + (x*4)    ),
             CharVector.sub (m, off + (x*4) + 1),
             CharVector.sub (m, off + (x*4) + 2),
             CharVector.sub (m, off + (x*4) + 3))

      fun loop (a, b, c, d) off =
          if off = len then (a, b, c, d)
          else loop (doblock (a, b, c,d) (mkx off)) (off + 64)

      val (a, b, c, d) = loop (a, b, c, d) 0
    in
      implode (w2b a @ w2b b @ w2b c @ w2b d)
    end

  fun md5 m = md5_advanced {len = size m, msg = m}

  val digits = "0123456789ABCDEF"
  fun bintohex s =
    String.translate (fn c =>
                      implode [CharVector.sub (digits, ord c div 16),
                               CharVector.sub (digits, ord c mod 16)]) s
end

structure Uses :
sig
  exception UsesError of string

  val uses : string -> unit
  val usesFile : string -> unit
  val collectFileListFromModStrFiles : string -> (string * string) list

  (*val canonicalName : string -> string*)
  (*val isLoaded : string -> bool*)
  val markAsLoadedFile : string -> unit
  val prependToPath : string -> unit
  val appendToPath : string -> unit
  val getLoadPaths : unit -> string list
  val setLoadPaths : string list -> unit

  val getLoadedFiles : unit -> (string * string) list
  val clearLoadedFiles : unit -> unit

  (* dumpUseRel relPath *)
  val dumpUseRel : string -> string
  val dumpUse : unit -> string
end =
struct
  structure Path = OS.Path
  structure FileSys = OS.FileSys

  exception UsesError of string

  fun log m = print ("SML Require Debug: " ^ m)
  fun log1 m = print ("SML Require: " ^ m)


  (* filename, canonical name (md5 hash) *)
  type loaded_files = (string * string) list

  val loadedFiles : loaded_files ref = ref []

  fun getLoadedFiles () = !loadedFiles
  fun clearLoadedFiles () = loadedFiles := []

  fun getCanonicalName fileName =
    (* fileName |> MissingIO.slurp |> MD5.md5 |> MD5.bintohex *)
    (MD5.bintohex o MD5.md5 o slurp) fileName

  fun markAsLoadedFile fileName =
  let
    val cname = getCanonicalName fileName
  in(
    loadedFiles := (fileName, cname) :: (!loadedFiles);
    log ("Marking the file \"" ^ fileName ^ "\" with canonical name (MD5) " ^
        cname ^ " as loaded"))
  end
  fun isLoaded fileName =
    exists ((fn c => fn (_, c') => c = c') (getCanonicalName fileName)) (!loadedFiles)


  fun dumpUseRel relPath =
  let
    val paths =
      map (fn (p,_) => OS.Path.mkRelative {path = p, relativeTo = relPath})
        (Missing.reverse (!loadedFiles))
    val useP = map (fn p => "use \""^ p ^ "\";\n") paths
  in
    concat useP
  end

  fun dumpUse () =
    concat (map (fn (p,_) => "use \""^ p ^ "\";\n")
                (Missing.reverse (!loadedFiles)))


  type load_paths = string list

  val loadPaths : load_paths ref = ref []

  fun appendToPath path = loadPaths := (!loadPaths) @ [path]
  fun prependToPath path = loadPaths := path :: (!loadPaths)
  fun getLoadPaths () = !loadPaths
  fun setLoadPaths pths = loadPaths := pths

  fun pathsToStr () =
  let
    fun enc p = "\"" ^ p ^ "\""
    fun str [] = ""
      | str [p] = p
      | str (p1::p2::paths) = (enc p1) ^ ", " ^ (enc p2) ^ (str paths)
  in
    "[" ^ (str (!loadPaths)) ^ "]"
  end



  val smlExtensions = ["ML", "sml"]


  fun modStrToComp modStr = String.fields (fn c => c = #"/") modStr
  fun modStrToPath modStr =
    Path.toString {isAbs = false,
                   vol   = Path.getVolume Path.currentArc,
                   arcs  = modStrToComp modStr}

  fun fileExists file = FileSys.access (file, [])


  fun findFileWithExt modStrPath [] = NONE
    | findFileWithExt modStrPath (ext::exts) =
  let
    val filePath = Path.joinBaseExt {base = modStrPath, ext = SOME ext}
  in
    if fileExists filePath
        then SOME filePath
        else findFileWithExt modStrPath exts
  end

  fun findFile modStrPath =
    if fileExists modStrPath
        then SOME modStrPath
        else findFileWithExt modStrPath smlExtensions


  (*fun resolveLocalModStr modStr = findFile (modStrToPath modStr)*)
  fun resolveLocalModStr fileName =
    if fileExists fileName
        then SOME fileName
        else NONE

  fun resolvePathModStr modStr [] = NONE
    | resolvePathModStr modStr (path::paths) =
  let
    val p1 = Path.fromString path
    val p2 = Path.fromString (modStrToPath modStr)
    val p = Path.toString
        {isAbs = #isAbs p1, vol = #vol p1, arcs = (#arcs p1) @ (#arcs p2)}
  in
    case findFile p of
         NONE => resolvePathModStr modStr paths
       | SOME f => SOME f
  end


  fun resolveModStr modStr =
    if String.isPrefix "@" modStr
        then resolveLocalModStr (String.extract (modStr,1,NONE))
        else resolvePathModStr modStr (!loadPaths)


  exception ParseError of string

  type stream = string * int

  val eos = Char.chr 0

  fun next s =
  let
    val (str,pos) = !s
  in
    if pos = String.size str
        then eos
        else (s := (str,pos+1); (String.sub (str,pos)))
  end

  fun peek s =
  let
    val (str,pos) = !s
  in
    if pos = String.size str
        then eos
        else (String.sub (str,pos))
  end

  fun matchStr s str = 
  let
    val i = 0
    val l = String.size str
  in
    while i <> l do
        if next s = String.sub (str, i)
            then ()
            else raise ParseError "Expected '' but found ''"
  end

  fun consumeWS s =
    if Char.isSpace (peek s)
        then (next s; consumeWS s)
        else ()


  fun consumeWS1 s =
    if Char.isSpace (peek s)
        then next s
        else raise ParseError ("White space expected but was found")

  fun parseMod s =
    if Char.isGraph (peek s)
        then (Char.toString (next s)) ^ parseMod s
        else ""

  fun parseMods' s =
  let
    val m = parseMod s
    val _ = consumeWS s
  in
    if peek s = #","
        then (next s; m :: (parseMods' s))
        else []
  end

  fun parseMods s =
  let
    val _ = matchStr s "require"
    val _ = consumeWS s
    val m = parseMods' s
  in
    m
  end

  fun parseReq s =
  let
    val _    = consumeWS s
    val _    = matchStr s "(*"
    val _    = consumeWS s
    val mods = parseMods s
    val _    = consumeWS s
    val _    = matchStr s "*)"
  in
    mods
  end


  (*
    <req-clause> ::= `require' <word> (`,' <word>)*

    <mods> ::= <mod> <mod-list>
    <mod-list> ::= <empty> | `,' <mod> <mod-list>
  *)



  fun readUsesFromFile filename =
  let
    val fh    = TextIO.openIn filename
    val fs    = ParserStreamIO.make fh
    val files = parse (usesParser ()) fs
    val ()    = TextIO.closeIn fh
  in
    case files of
         LEFT (m as (Parser.Error msg,s)) => raise UsesError (errormsg m ^ " in file " ^ filename) 
       | LEFT (Parser.Fail msg,_)  => []
       | RIGHT (fs,_)              => fs
  end


  fun collectFileListFromModStrFiles modStr =
  let
    val loaded = ref []

    fun isVisited cname visited = List.exists (fn (_,_,c1) => cname = c1) visited

    fun strVis [] = ""
      | strVis [(v,_,_)] = v ^ "->"
      | strVis ((v1,_,_)::(v2,_,_)::vs) = strVis vs ^ v2 ^ " -> " ^ v1

    fun loadFile modStr visited =
    let
      val path = resolveModStr modStr
    in
      (case path of
           NONE => raise UsesError
                ("Module '" ^ modStr ^ "' not found in path " ^ pathsToStr () ^
                (case visited of
                     [] => ""
                   | _ => " while visiting " ^ strVis visited))
         | SOME p =>
             (let
               val c = getCanonicalName p
             in
               if isVisited c visited
                  then
                    raise UsesError ("Circular dependency found: " ^
                                     strVis ((modStr,p,c)::visited))
                  else if isLoaded p
                    then (log ("The file \"" ^ p ^ "\" is marked as loaded"); ())
                  else
                    let
                      val modStrs = readUsesFromFile p
                      val () = log ("Visiting file " ^ p ^ " with canonical name " ^ c)
                      val vis = (modStr, p, c)::visited
                      val () = forall (fn ms => loadFile ms vis) modStrs
                      val () = loaded := (!loaded) @ [(modStr,p)]
                      val _ = markAsLoadedFile p
                    in () end
             end))
    end

    val () = loadFile modStr []
  in
    !loaded
  end

  fun printErr str = TextIO.output (TextIO.stdErr, str)

  fun uses' modStr =
  let
    val files = collectFileListFromModStrFiles modStr
  in
    forall (fn (m,f) =>
        (log1 ("Loading module \"" ^ m ^ "\" resolved as the file \"" ^ f ^ "\"");
         use f)) files
  end


  fun uses modStr =
    uses' modStr
        handle (IO.Io {name, ...}) =>
            printErr ("\nError: could not read the file \"" ^ name ^ "\"\n")

  fun usesFile filename = uses ("@" ^ filename)

end;



