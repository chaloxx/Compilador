structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans

type expty = {exp: exp, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt RW), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=mainLevel, label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=mainLevel, label="ord",
		formals=[TString], result=TInt RW, extern=true}),
	("chr", Func{level=mainLevel, label="chr",
		formals=[TInt RW], result=TString, extern=true}),
	("size", Func{level=mainLevel, label="size",
		formals=[TString], result=TInt RW, extern=true}),
	("substring", Func{level=mainLevel, label="substring",
		formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
	("concat", Func{level=mainLevel, label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=mainLevel, label="not",
		formals=[TInt RW], result=TInt RW, extern=true}),
	("exit", Func{level=mainLevel, label="exit",
		formals=[TInt RW], result=TUnit, extern=true})
	])

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TInt _) (TInt _) = true
  | tiposIguales a b = (a=b)

fun tiposIgualesList ([],[]) = true
    | tiposIgualesList (x::xs,y::ys) = (tiposIguales x y) andalso tiposIgualesList (xs,ys)
    | tiposIgualesList (x::xs,[]) = false
    | tiposIgualesList ([],y::ys) = false


fun searchList([],_) = NONE
    | searchList((s2,x)::xs,s) = if s = s2 then SOME x
	                             else searchList (xs,s)




fun zip [] _  = []
    | zip _ [] = []
    | zip (x::xs) (y::ys) = ((x,y)::(zip xs ys))



fun checkDuplicates ys = let fun aux  rs [] = NONE
                              | aux rs ((h:string*int)::hs) = (case List.find (fn x => x = #1 h) rs of
															                                    NONE => aux ((#1 h)::rs) hs
																										            | SOME_ => SOME h)
												 in aux [] ys
												 end




fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
            fun msg1(f) = "Los tipos de los argumentos de " ^ f ^ " no coinciden con los tipos de sus parámetros"
            fun msg2(f) = f ^ " no es una función"
            fun msg3(f) = f ^ " no está definida"
						val msg4 = "El tipo de la variable no coincide con el de la expresión"
						fun msg5(v) = v ^ " no es una variable"
						fun msg6(v) = "El tipo " ^ v ^ " no está definido"
						val msg7 = "Los tipos no coindicen"
						val msg8 = "El tamaño debe tener tipo entero"
						fun msg9(s) = s ^ " no es un arreglo"
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=SCAF, ty=TUnit}
		| trexp(NilExp _)= {exp=SCAF, ty=TNil}
		| trexp(IntExp(i, _)) = {exp=SCAF, ty=TInt RW}
		| trexp(StringExp(s, _)) = {exp=SCAF, ty=TString}
		| trexp(CallExp({func, args}, nl)) = (case tabBusca(func,venv) of
                                                        SOME (Func reg) => let val t1 = map trexp args
                                                                               val t2 = map (fn x => #ty x) t1
                                                                           in if tiposIgualesList (t2,#formals reg) then {exp=SCAF, ty= #result reg}
                                                                              else error (msg1(func),nl)
                                                                           end
                                                        |SOME _  => error (msg2(func),nl)
                                                        |NONE => error (msg3(func),nl))


		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
                        in     if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt RW}
			       else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| MinusOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| TimesOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| DivideOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| LtOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| LeOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| GtOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| GeOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case t of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)

				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar [] [] = ()
				  | verificar (c::cs) [] = error("Faltan campos", nl)
				  | verificar [] (c::cs) = error("Sobran campos", nl)
				  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty (!t) then verificar cs ds
							 else error("Error de tipo del campo "^s, nl)
				val _ = verificar cs tfields
			in
				{exp=SCAF, ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=SCAF, ty=tipo } end
		(*| trexp(AssignExp({var=SimpleVar s, exp}, nl)) = (case tabBusca(s,venv) of
		                                                  NONE => error(msg3(s),nl)
																											|SOME (Var {ty=t}) => let val {ty=t2,...} = trexp exp
																											                      in if tiposIguales t t2 then {exp=SCAF, ty=TUnit}
																																               else error(msg4(s),nl)
																																				  end
																											| SOME _ => error(msg5(s),nl))*)

		| trexp(AssignExp({var, exp}, nl)) = let val {ty=t,...} = trvar(var,nl)
                                             val {ty=t2,...} = trexp(exp)
																				 in if tiposIguales t t2 then  {exp=SCAF, ty=TUnit}
																				    else error(msg4,nl)
																				 end


		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tytest=TInt RW andalso tiposIguales tythen tyelse then {exp=SCAF, ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tytest=TInt RW andalso tythen=TUnit then {exp=SCAF, ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if (#ty ttest) = TInt RW andalso #ty tbody = TUnit then {exp=SCAF, ty=TUnit}
				else if (#ty ttest) <> TInt RW then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) = (*let  val {exp=explo,ty=tylo} = trexp lo
		                                                        val {exp=exphi,ty=tyhi} = trexp hi
																														(*val _ = preForWhile()*)
																														val venv' = tabInserta(var,TInt RO,venv)
																														val {exp=expbody,ty=tybody} = (transExp (venv',tenv)) body*)
			{exp=SCAF, ty=TUnit} (*COMPLETAR*)
		| trexp(LetExp({decs, body}, _)) =
			let
				val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in
				{exp=SCAF, ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=SCAF, ty=TUnit} (*COMPLETAR*)
		| trexp(ArrayExp({typ, size, init}, nl)) = (case tabBusca(typ,tenv) of
		                                             NONE => error(msg6(typ),nl)
																								 | SOME (TArray (t,_)) => let val {ty=t2,...} = trexp init
																								                          in if tiposIguales (!t) t2 then let val {ty=ts,...} = trexp size
																																					                                in if tiposIguales ts (TInt RW) then {exp=SCAF, ty=TUnit}
																																																					   else error(msg8,nl)
																																																					end
																																						 else error(msg7,nl)
																																					end
																								| SOME _ => error(msg9(typ),nl))

		and trvar(SimpleVar s, nl) = (case tabBusca(s,venv) of
		                              NONE => error(msg3(s),nl)
									  | SOME (Var {ty=t}) => {exp=SCAF,ty=t}
									  | SOME _ => error(s ^ "no es una variable simple",nl))


		| trvar(FieldVar(v, s), nl) = (case trvar(v,nl) of
		                                {ty=(TRecord (tyl,_)),...} => let val tyl2 = map (fn (x,y,_) => (x,y)) tyl
		                                                              in (case searchList(tyl2,s) of
									                                       NONE => error(msg3(s),nl)
										                                   |SOME typ  => {exp = SCAF,ty=(!typ)})
								                                       end
								        |_ => error(s ^ "no es campo de un record definido",nl))

		| trvar(SubscriptVar(v, e), nl) = (case trvar(v,nl) of
		                                 {ty=TArray (typ,_),...} => let val {ty=t,...} = trexp e
										                            in if tiposIguales t (TInt RW) then {exp=SCAF,ty=(!typ)}
																       else error("La expresion no es de into int",nl)
																    end
										 |_ => error("La variable no es de tipo Array",nl))

		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = let val {ty=t,...} = trexp init
		                                                                        val venv' = tabRInserta(name,Var {ty=t},venv)
																		    in (venv',tenv,[])
																			end

		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) = let val {ty=t,...} = trexp init
		                                                                   in (case tabBusca(s,tenv) of
																		        NONE => error("El tipo " ^ s ^ " no existe",pos)
																				|SOME t2 => if t = t2 then let val venv' = tabRInserta(name,Var {ty=t},venv)
																		                                   in (venv',tenv,[])
																			    			               end

																		                     else error("El tipo de " ^ s ^ " no coincide con el de la expresion",pos))
																		   end

		| trdec (venv,tenv) (FunctionDec fs) =  let val np = map (fn (reg,pos) => (#name reg,pos)) fs
		                                        in (case checkDuplicates np of
																						     NONE => let  val funList  = map (trfun tenv) fs
																								              val names = map (fn (n,_) => n) np
																															val funcsEntry = zip names funList
																															val venv' = List.foldl (fn ((s,f),e) => tabRInserta(s,f,e)) venv funcsEntry
																															val _ = map (fn (r,_) => trexpBody r venv' tenv) fs
																								         in (venv',tenv,[])
																												 end
																								|SOME (f,p) => error(f^" ya está declarada en este batch",p))
																						end
		| trdec (venv,tenv) (TypeDec ts) =
			(venv, tenv, []) (*COMPLETAR*)

		and   trfun tenv  dec = let  val (r,nl) = dec
		                             val (prueba : Tipo list) = map (trparam nl tenv) (#params r)
		                        in (case  #result r of
									                NONE => Func {level = mainLevel, label = #name r,formals = prueba, result = TUnit, extern = false}
							                   | SOME s => (case tabBusca(s,tenv) of
								                               NONE => error(s ^" no es un tipo",nl)
					   						                       |SOME t  => Func {level = mainLevel, label = #name r,formals = prueba, result = t, extern = false} ))
		                        end



  and trparam nl tenv p = (case #typ p  of
		 			  								NameTy s => (case tabBusca(s,tenv) of
		 				     						               NONE => error(s^ " no es un tipo",nl)
		 					  									        |SOME t => t)
		 						   		      |_ => error("No es un NameTy",nl))

  and trexpBody r venv tenv = let val name = #name r
			                            val nameParams = map #name (#params r)
         												  val typsParams = (case tabBusca(name,venv) of
					    										                     NONE => raise Fail "Basura"
							    																		 |SOME (Func f) => #formals f
																											 | SOME _ => raise Fail "Basura")
									    						val ntParams = zip nameParams typsParams
											    				val venv' = List.foldl (fn ((s,t),v) => tabRInserta(s,Var {ty=t},v)) venv ntParams
													    in (transExp (venv',tenv)) (#body r)
													    end



	in trexp end
fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=NONE, body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "bien!\n" end
end
