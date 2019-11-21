structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs

exception breakexc
exception divCero

type level = {parent:frame option , frame: frame, level: int}
type access = tigerframe.access

fun setAccesses (lvl:level) accessList = let val frame' = tigerframe.setFrame accessList (#frame lvl)
							  								         in {parent = #parent lvl, frame=frame', level=(#level lvl)}
																         end

type frag = tigerframe.frag
val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE, frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()}
fun newLevel{parent={parent, frame, level}, name, formals} =
	{
	parent=SOME frame,
	frame=newFrame{name=name, formals=(true::formals)},
	level=level+1}
fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
	Ex of tigertree.exp
	| Nx of tigertree.stm
	| Cx of label * label -> tigertree.stm



fun seq [] = EXP (CONST 0)
	| seq [s] = s
	| seq (x::xs) = SEQ (x, seq xs)


fun unEx (Ex e) = e
	| unEx (Nx s) = ESEQ(s, CONST 0)
	| unEx (Cx cf) =
	let
		val r = newtemp()
		val t = newlabel()
		val f = newlabel()
	in
		ESEQ(seq [MOVE(TEMP r, CONST 1),
			cf (t, f),
			LABEL f,
			MOVE(TEMP r, CONST 0),
			LABEL t],
			TEMP r)
	end

fun unNx (Ex e) = EXP e
	| unNx (Nx s) = s
	| unNx (Cx cf) =
	let
		val t = newlabel()
		val f = newlabel()
	in
		seq [cf(t,f),
			LABEL t,
			LABEL f]
	end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
	| unCx (Cx cf) = cf
	| unCx (Ex (CONST 0)) =
	(fn (t,f) => JUMP(NAME f, [f]))
	| unCx (Ex (CONST _)) =
	(fn (t,f) => JUMP(NAME t, [t]))
	| unCx (Ex e) =
	(fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun Ir(e) =
	let	fun aux(Ex e) = tigerit.tree(EXP e)
		| aux(Nx s) = tigerit.tree(s)
		| aux _ = raise Fail "bueno, a completar!"
		fun aux2(PROC{body, frame}) = aux(Nx body)
		| aux2(STRING(l, "")) = l^":\n"
		| aux2(STRING("", s)) = "\t"^s^"\n"
		| aux2(STRING(l, s)) = l^":\t"^s^"\n"
		fun aux3 [] = ""
		| aux3(h::t) = (aux2 h)^(aux3 t)
	in	aux3 e end
fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la u'ltima etiqueta para un break *)
local
	val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
	val pushSalida = tigerpila.pushPila salidas
	fun popSalida() = tigerpila.popPila salidas
	fun topSalida() =
		case tigerpila.topPila salidas of
		SOME l => l
		| NONE => raise Fail "break incorrecto!"
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
	let	val label = STRING(name(#frame level), "")
		val body' = PROC{frame= #frame level, body=unNx body}
		val final = STRING(";;-------", "")
	in	datosGlobs:=(!datosGlobs@[label, body', final]) end
fun getResult() = !datosGlobs

fun stringLen s =
	let	fun aux[] = 0
		| aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
		| aux(_::t) = 1+aux(t)
	in	aux(explode s) end

fun stringExp(s: string) =
	let	val l = newlabel()
		(*val len = ".long "^makestring(stringLen s)*)
		(*val str = ".string \""^s^"\""*)
		val _ = datosGlobs:=(!datosGlobs @ [STRING(l,s)])
	in	Ex(NAME l) end
fun preFunctionDec() =
	(pushSalida(NONE);
	actualLevel := !actualLevel+1)
fun functionDec(e, l, proc) =
	let	val body =
				if proc then unNx e
				else MOVE(TEMP rv, unEx e)
		val body' = procEntryExit1(#frame l, body)
		val () = procEntryExit{body=Nx body', level=l}
	in	Ex(CONST 0) end
fun postFunctionDec() =
	(popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)



val slOffset = 0

fun  calcularFrame(0,exp) = exp
     |calcularFrame(salto,exp) = let val exp' = MEM(BINOP(PLUS,exp,CONST slOffset))
	                                    in calcularFrame(salto-1,exp')
										end


fun simpleVar(fnivel,acc, nivel) =
	(case acc of
		InReg temp => Ex (TEMP temp)
	   |InFrame offset => let val exp = calcularFrame(fnivel-nivel,TEMP fp)
	                      in Ex (MEM(BINOP(PLUS,exp, CONST offset)))
						  end
	  )


fun varDec(acc) = simpleVar(getActualLev(),acc, getActualLev())

fun fieldVar(var, field) = Ex (MEM(BINOP(PLUS,unEx(var),CONST field)))

fun subscriptVar(arr, ind) =
let
	val a = unEx arr
	val i = unEx ind
	val ra = newtemp()
	val ri = newtemp()
in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		MOVE(TEMP ri, i),
		EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
		MEM(BINOP(PLUS, TEMP ra,
			BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end




fun comparar ((_,x),(_,y)) = Int.compare (x,y)


fun recordExp l = let val lOrd =  Listsort.sort comparar l
                      val lOrd' = map (fn (x,_) => unEx x) lOrd
                  in Ex(CALL(NAME "_allocRecord",[CONST (length lOrd')] @ lOrd'))
				  end


fun arrayExp{size, init} =
let
	val s = unEx size
	val i = unEx init
in
	Ex (externalCall("allocArray", [s, i]))
end


fun calcularSL(calleeLvl,callerLvl,exp) = if callerLvl = calleeLvl then MEM(BINOP(PLUS,exp,CONST slOffset))
                                          else if callerLvl < calleeLvl then exp
										       else calcularFrame(callerLvl-calleeLvl,exp)


fun callExp (calleeLvl,name,true,isproc,lev:level,ls) = let val exps = map unEx ls
                                                            val call = CALL(NAME name,exps)
                                                        in if isproc then  Nx ( EXP call)
											               else Ex call
											            end
   | callExp (calleeLvl,name,false,isproc,lev:level,ls) = let val exps = map unEx ls
		                                                      val sl = calcularSL(calleeLvl,#level lev,TEMP fp)
															  val call = CALL(NAME name,(sl::exps))
														  in if isproc then Nx (EXP call)
														     else Ex call
														  end


fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

fun breakExp() = Nx (JUMP (NAME (topSalida()),[topSalida()]))



fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
	| seqExp (exps:exp list) =
		let
			fun unx [e] = []
				| unx (s::ss) = (unNx s)::(unx ss)
				| unx[] = []
		in
			case List.last exps of
				Nx s =>
					let val unexps = map unNx exps
					in Nx (seq unexps) end
				| Ex e => Ex (ESEQ(seq(unx exps), e))
				| cond => Ex (ESEQ(seq(unx exps), unEx cond))
		end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

fun whileExp {test: exp, body: exp, lev:level} =
let
	val cf = unCx test
	val expb = unNx body
	val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
in
	Nx (seq[LABEL l1,
		cf(l2,l3),
		LABEL l2,
		expb,
		JUMP(NAME l1, [l1]),
		LABEL l3])
end

fun forExp {lo, hi, var, body} =
	let val exBody = unNx body
	    val exLo = unEx lo
			val exHi = unEx hi
			val thi = newtemp()
			val exVar = unEx var
			val (start,intermedio,fin) = (newlabel(), newlabel(),topSalida())
	in Nx (seq [MOVE(exVar,exLo),MOVE(TEMP thi,exHi),CJUMP(GT,exVar,TEMP thi,fin,start),
	            LABEL start,exBody,CJUMP(GE, exVar,TEMP thi,fin,intermedio),
		     	LABEL intermedio, MOVE(exVar,BINOP(PLUS,exVar,CONST 1)), JUMP(NAME start,[start]),
				LABEL fin])
	end



fun ifThenExp{test, then'} =
	let val cf = unCx test
	    val body = unNx then'
	    val (l1,l2) = (newlabel(),newlabel())
	in Nx (seq [cf(l1,l2),LABEL l1, body,LABEL l2])
	end

fun ifThenElseExp {test,then',else'} =
 let val cf = unCx test
		 val bodyIf = unEx then'
		 val bodyElse = unEx else'
		 val (l1,l2) = (newlabel(),newlabel())
		 val t = newtemp()
  in Ex (ESEQ(seq [ cf(l1,l2), LABEL l1, MOVE(TEMP t, bodyIf), LABEL l2, MOVE(TEMP t, bodyElse) ], TEMP t))
  end





fun ifThenElseExpUnit {test,then',else'} =
	let val cf = unCx test
		 val bodyIf = unNx then'
		 val bodyElse = unNx else'
		 val (l1,l2) = (newlabel(),newlabel())
	 in Nx (seq [cf(l1,l2),LABEL l1, bodyIf,LABEL l2,bodyElse])
	 end

fun assignExp{var, exp} =
	let
		val v = unEx var
		val vl = unEx exp
	in
		Nx (MOVE(v,vl))
	end


(*Agregamos*)
fun transOpInt PlusOp = PLUS
 | transOpInt MinusOp  = MINUS
 | transOpInt TimesOp = MUL
 | transOpInt DivideOp  = DIV
 | transOpInt _ = raise Fail "Cualquieraaaa"

(*Agregamos*)
fun transOpRel EqOp = EQ
 | transOpRel NeqOp = NE
 | transOpRel LtOp = LT
 | transOpRel LeOp = LE
 | transOpRel GtOp = GT
 | transOpRel  GeOp = GE
 | transOpRel _ = raise Fail"Cualquieraaaa"



fun binOpIntExp {left, oper, right} =
	let val leftExp = unEx left
	    val rightExp = unEx right
			val oper' = transOpInt oper
	in Ex (BINOP(oper',leftExp,rightExp))
	end

fun binOpIntRelExp {left, oper, right} =
  let val oper' = transOpRel oper
	    val leftExp = unEx left
			val rightExp = unEx right
	    val cjump = fn (t,f) => CJUMP (oper',leftExp,rightExp,t,f)
   in Cx cjump
   end

fun binOpStrExp {left,oper,right} = let val exLeft = unEx left
                                        val exRigth = unEx right
										val exOper = transOpRel oper
										val call =  CALL (NAME "_stringCompare",[exLeft,exRigth])
										val cjump = fn (t,f) => CJUMP (exOper,call,CONST 0,t,f)
								    in Cx cjump
									end


end
