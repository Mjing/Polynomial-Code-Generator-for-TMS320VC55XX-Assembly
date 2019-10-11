use "symex.sml";
use "code_gen.sml";

open SYMEX;
Control.Print.printDepth := 100;

(*Generate a lagrange Polynomial with roots*)
val x = lagrange 3 [COEFF "f5-f0-5.d" ,COEFF "f4-f0-4d", COEFF "f3-f0-3d", COEFF "f2-f0-2d", COEFF "f1-f0-d"]
(*Value map of named coeffiecients*)
val table = [( "f5-f0-5.d", 5) ,( "f4-f0-4d",4), ( "f3-f0-3d",3), ( "f2-f0-2d",2), ( "f1-f0-d",1), ("f0", 0), ("d", 6)]
val p = MULT(x, VAR 2);
val approx_6 = reduce ( evaluate (ICOEFF 1) (ADD(p, ADD(MULT(COEFF "d", VAR 1), COEFF "f0"))));

val DSP = compile [approx_6] table;

printDSP DSP ;

