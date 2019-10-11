use "symex.sml";
open SYMEX;

local 
	fun lagrange_helper 0 0 f = f
		|lagrange_helper i 0 f = ADD(VAR 1, ICOEFF ~1)
		|lagrange_helper i j f = if (i=j) then MULT (lagrange_helper i (j-1) f, f) else MULT( ADD(VAR 1, ICOEFF (~(j+1)) ), lagrange_helper i (j-1) f);

in
	fun lagrange j [] = ICOEFF 0
		|lagrange j (h::t) = let 
			fun helper j ([h])  = lagrange_helper 0 j h
				|helper j (h::t) = ADD(lagrange_helper ((length (t))) j h, (helper j t))
			in
				helper (length(t)) (h::t)
			end
end

(*DSP Assembly datatype: Constructor for each operator*)
datatype DSPASM = AC of int | AR of int | T of int  | IMM of real
		|Load1 of DSPASM | LOAD2 of (DSPASM * DSPASM) | PADDR of DSPASM
		|LADDR of (DSPASM * int)
		|ADD1 of DSPASM  |DSPADD of (DSPASM * DSPASM)
		|MULT1 of DSPASM| MULT2 of (DSPASM) | DSPMULT of (DSPASM*DSPASM)

(*Symex to DSPASM compiler, compiles constant symex expressions into DSP-code*)
local
	fun from_table [(s,loc)] x = loc
		|from_table ((s,loc)::table) x = if (x=s) then loc else from_table table x 
	
	fun operate_coeff 	table (ADD1 (AC 1)) (ICOEFF x) = [DSPADD (AC 1, IMM (real x))]
		|operate_coeff 	table (ADD1 (AC 1)) (DIV (ICOEFF x)) = [DSPADD(AC 1, IMM (1.0/real(x)))]
		|operate_coeff 	table (ADD1 (AC 1)) (COEFF x) = [LADDR (AR 4, from_table table x), DSPADD(AC 1, PADDR(AR 4))]
		|operate_coeff 	table (MULT1 (AC 2)) (ICOEFF x) = [LOAD2 (AC 2, IMM(real x))]
		|operate_coeff table (MULT1 (AC 2))  (DIV(ICOEFF(x))) = [LOAD2 (AC 2, IMM(1.0/real(x)))]
		|operate_coeff table (MULT1 (AC 2)) (COEFF x) = [LADDR(AR 4, from_table table x), LOAD2(AC 2, PADDR(AR 4))]
		|operate_coeff 	table (MULT2 (AC 2)) (ICOEFF x) = [DSPMULT (AC 2, IMM(real x))]
		|operate_coeff table (MULT2 (AC 2))  (DIV(ICOEFF(x))) = [DSPMULT (AC 2, IMM(1.0/real(x)))]
		|operate_coeff table (MULT2 (AC 2)) (COEFF x) = [LADDR(AR 4, from_table table x), DSPMULT(AC 2, PADDR(AR 4))]

	fun is_add (ADD _) = true
		|is_add _ = false
	fun is_mult (MULT _) = true
		|is_mult _ = false

	fun compile_helper _ _ [] l = l
		|compile_helper l table ((ADD(x,y))::t) dsp_code = let 
			val c1 = if(is_mult x) then (compile_helper ([MULT1 (AC 2)]) table [x] [])  @ [(DSPADD (AC 1 , AC 2))] 
			else (compile_helper [ADD1 (AC 1)] table [x] []);
			val c2 =  if(is_mult y) then (compile_helper [MULT1 (AC 2)] table [y] [] ) @ [(DSPADD (AC 1, AC 2))]
			else compile_helper [ADD1 (AC 1)] table [y] [] 
		in
			compile_helper l table t (dsp_code @ c1 @ c2)
		end
		|compile_helper ((MULT1 (AC 2))::t) table ((MULT(x,y))::code) dsp_code  = 
		let
			val c1 = compile_helper [MULT1 (AC 2)] table [x] [] ;
			val c2 = compile_helper [MULT2 (AC 2)] table [y] [] 
		in
			compile_helper t table code (dsp_code @ c1 @ c2)
		end
		|compile_helper ((MULT2 (AC 2))::t) table ((MULT(x,y))::code) dsp_code  = 
		let
			val c1 = compile_helper [MULT2 (AC 2)] table [x] [] ;
			val c2 = compile_helper [MULT2 (AC 2)] table [y] [] 
		in
			compile_helper t table code (dsp_code @ c1 @ c2)
		end
		|compile_helper (h::t) table (x::code) dsp_code = compile_helper t table code (dsp_code @ (operate_coeff table h x))
in
	fun compile x table= compile_helper [ADD1 (AC 1)] table x [LOAD2(AC 1, IMM(0.0))]
end;


(*DSPASM to TMS-ASM compiler*)
local
	fun helper (AC i) = ("AC"^Int.toString(i))
		|helper (AR i)= ( "AR"^ Int.toString(i))
		|helper (IMM r)=  ("#"^(Real.toString(r)))
		|helper (PADDR x) = ("*"^(helper x))
in
	fun printDSP [] = (print "\n")
		|printDSP ((DSPADD(x,y))::t) = (print ((helper x)^" = "^(helper x)^" + "^(helper y)^"\n"); printDSP t)
		|printDSP ((DSPMULT(x,y))::t) = (print ((helper x)^" = "^(helper x)^ " << #16\n"^ (helper x)^" = "^(helper x) ^" * "^ (helper y) ^ "\n"
			^(helper x)^" = "^(helper x)^ " << #-15\n"); printDSP t)
		|printDSP ((LOAD2(x,y))::t) = (print ((helper x)^" = "^(helper y) ^ "\n"); printDSP t)
		|printDSP ((LADDR(x,y))::t) = (print ("X"^(helper x)^" = " ^  "#signal\n" ^ "X"^(helper x)^" = " ^ "X"^(helper x)^ "+" ^Int.toString(y)^ "\n"); printDSP t)
end;

 
