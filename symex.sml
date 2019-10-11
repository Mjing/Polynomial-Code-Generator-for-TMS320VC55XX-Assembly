structure SYMEX = 
struct
	(*Data type for polyomial in variable x*)
	datatype POLY = 
		ICOEFF of int
		| COEFF of string
		| VAR of int
		| ADD of POLY*POLY
		| MULT of POLY*POLY
		(*DIV x => 1/x coeff*)
		| DIV of POLY


		(*Checks if the input is constant*)
		fun coeff (COEFF _) = true
			|coeff (ICOEFF _) = true
			|coeff (VAR _) = false
			|coeff (DIV x ) = coeff x
			|coeff (ADD(x,y)) = (coeff x) andalso (coeff y)
			|coeff (MULT(x,y))= (coeff x) andalso (coeff y)
			(*|coeff (POWER(x,_))= coeff(x)*)

		


		(*Sum of products*)
		fun sum_of_products (MULT(x,ADD(y,z))) = ADD(sum_of_products (MULT(x,y)),sum_of_products (MULT(x,z)))
			|sum_of_products (MULT(ADD(x,y),z))= ADD(sum_of_products (MULT(x,z)),sum_of_products (MULT(y,z)))
			|sum_of_products (ADD(x,y)) = ADD(sum_of_products x, sum_of_products y)
			
			|sum_of_products (MULT (VAR x, VAR y)) = VAR (x+y)
			
			|sum_of_products (MULT (VAR x, y)) = sum_of_products (MULT (y,VAR x))
			
			|sum_of_products (MULT(x,y)) = let
				fun apply_again (MULT((ADD _) , _)) = true
					|apply_again(MULT(_,ADD _))= true
					|apply_again _ = false;

				fun combine (VAR x) (MULT(y, VAR z)) = MULT(y,VAR(x+z))
					|combine (MULT(x,VAR y)) (VAR z) = MULT(x,VAR(y+z))
					|combine x (MULT(y, VAR z)) = MULT(MULT(x,y),VAR z)
					|combine x y = MULT(x,y)

				val x' = ( sum_of_products x);
				val y' = ( sum_of_products y)
			in
				if (apply_again(MULT(x',y'))) then sum_of_products (MULT(x',y'))
				else combine x' y'
			end
			|sum_of_products x = x


		local 
			fun eq_int i (ICOEFF j) = (i=j)
			|eq_int _ _ = false ;

			fun add_int (ICOEFF x) (ICOEFF y) = ICOEFF(x+y)
				|add_int (ICOEFF 0) x = x 
				|add_int x (ICOEFF 0) = x
				|add_int x y = ADD(x,y);

			fun mult_int (ICOEFF x) (ICOEFF y) = ICOEFF(x*y)

				|mult_int (ICOEFF x) y = if(x=0) then ICOEFF 0
				else if (x=1) then y else MULT (ICOEFF x,y)
				|mult_int y (ICOEFF x) = if(x=0) then ICOEFF 0
				else if (x=1) then y else MULT (ICOEFF x,y)
				|mult_int x y = MULT(x,y)

			fun div_by (ICOEFF 1) x = x
				|div_by x (MULT(y,z)) = let 
					val y' = div_by x y;
					val z' = div_by x z;
				in
					if ((y=y') andalso (z=z')) then MULT(y,z)
					else if (y = y') then MULT(y',z)
					else MULT(y,z')	 
				end

				|div_by x (ADD(y,z)) = ADD(div_by x y, div_by x z)
				
				|div_by x y = if(y=x) then ICOEFF 1 else y
			

		in
		(*Multiply and Addition by {1,0}*)		
			fun simplify (ADD(x,y)) = 
				let 
					val x' = simplify x ;
					val y' = simplify y 
				in
					add_int x' y'
				end


				|simplify (MULT(DIV(x),y)) = let 
					val sy = simplify y;
					val sx = simplify x;
					val y' = div_by sx sy 
				in
					if (y' = sy) then mult_int (DIV x) (simplify y) else sy 
				end

				|simplify (MULT(y, DIV x)) = let 
					val sy = simplify y;
					val sx = simplify x;
					val y' = div_by sx sy 
				in
					if (y' = sy) then mult_int (DIV x) (sy) else y' 
				end


				|simplify (MULT(x,y)) = mult_int (simplify x) (simplify y)
				

				|simplify (DIV  (ICOEFF 1)) = ICOEFF 1 

				|simplify x = x
		end

		fun max x y = if(x>y) then x else y;
			(*Only for sum of products form*)
		local 
				fun get_degree_helper (VAR j) = j
					|get_degree_helper (ADD(x,y)) = (max (get_degree_helper x) (get_degree_helper y))
					|get_degree_helper (MULT(x,y))= (get_degree_helper x) + (get_degree_helper y)
					|get_degree_helper x = 0
			in
				fun degree x = get_degree_helper x
		end

		fun get_coeff i (VAR y) = if (i=y) then (ICOEFF 1, ICOEFF 0) else (ICOEFF 0, ICOEFF 0)
				
				|get_coeff i (ADD(x,y)) = 
					let 
						val (x1, r1) = get_coeff i x;
						val (x2, r2) = get_coeff i y
					in
						(ADD(x1,x2), ADD(r1,r2))
					end
					
				
				|get_coeff i (MULT(x,y)) = 
					if(i = degree x) then  let 
						val (x', r') = (get_coeff i x)
					in 
						(MULT (x', y), MULT(r', y))
					end
					else if (i = degree y) then  let 
						val (x', r') = ( get_coeff i y)
					in 
						(MULT(x,x') , MULT(x,r'))
					end
					else (ICOEFF 0, MULT(x,y))
				
				|get_coeff _ x = (ICOEFF 0, x)


		(*Normal form : Sigma ai*xi *)
		fun normal_form x = let
			val x' = simplify (sum_of_products (simplify x));
			

			fun helper 1 x = let
					val (x',r') = get_coeff 1 x
				in
					ADD(MULT(x',VAR 1), r')
				end
				
				|helper 0 x = simplify x

				|helper i x = let 
					val (x',r') = get_coeff i x 
				in 
					ADD ( MULT(simplify x', VAR i), helper (i-1) r')
				end
		in
			simplify (helper (degree x') x')
		end	

		(*Differentiation of polynomial*)
		fun diff (VAR 1) = ICOEFF(1)
			|diff (VAR x) = if(x<0) then ICOEFF 0 else MULT(ICOEFF (x), VAR (x-1))
			|diff (ICOEFF _) = ICOEFF(0)
			|diff (COEFF _) = ICOEFF(0)
			|diff (DIV _) = ICOEFF (0)
			|diff (ADD(x,y)) = ADD(diff x, diff y)
			|diff (MULT(x,y)) = if ((coeff x) andalso (coeff y)) then ICOEFF(0)
				(*CHAIN RULE*)
				else if ((not (coeff x)) andalso (not(coeff y))) then ADD(MULT(diff x, y),MULT(x,diff y))
				else let 
						val x' = (if (coeff x) then x else diff x);
						val y' = (if (coeff y) then y else diff y);
					in 
						if((x' = ICOEFF 0)  orelse (ICOEFF 0 = y )) then ICOEFF(0)
						else if (ICOEFF 1 = x' ) then y'
						else if (ICOEFF 1 = y' ) then x'
						else MULT(x',y')
					end

		local
			fun helper(VAR x) =  MULT (DIV(ICOEFF (x+1)), VAR (x+1))
				
				|helper(ADD (x,y)) = ADD (helper x, helper y)
				|helper(MULT(x,y)) = 
				if (coeff (MULT(x,y))) then MULT(MULT(x,y), VAR 1)
				else if (coeff x) then MULT (x,helper y)
				else if (coeff y) then MULT (y, helper x)
				else ICOEFF (~1)
				|helper x = if(coeff x) then MULT(x,VAR 1) else ICOEFF(~1)
		in
			fun integrate x = helper (normal_form x)
		end

		fun reduce x = let
			val  x' = sum_of_products(normal_form x) ;
			(*gets all the products of sum of products*)
			fun mult_int (ICOEFF x) (ICOEFF y) = ICOEFF (x*y)
				|mult_int (DIV (ICOEFF x)) (DIV (ICOEFF y)) = DIV(ICOEFF (x*y))

			fun get_products (ADD(x,y)) = (get_products (x)) @ (get_products y)
				|get_products x = [x] 

			(*get all components of products (ICOEFF, DIV ,{coeff,var} list)*)
			fun get_components (ICOEFF x) = (ICOEFF x, DIV( ICOEFF 1), [])
				|get_components (DIV(ICOEFF x)) = (ICOEFF 1, DIV(ICOEFF x), [])
				|get_components (MULT(x,y)) = let
					val (ix,dx,lx) = get_components x; 
					val (iy,dy,ly) = get_components y
				in
					(mult_int ix iy, mult_int dx dy, lx @ ly)
				end
				(*Only case of COEFF is allowed*)
				|get_components x = (ICOEFF 1, DIV (ICOEFF 1) , [x])

			val components = map get_components (get_products x');

			fun unordered_equality [] [] = true  
				|unordered_equality (h1::t1) l = let
					fun present h [] = (false, [])
						|present h (h'::t) = if(h=h') then (true,t) else (
							let
								val (t, r) = present h t 
							in
								(t, h'::r)
							end)
					val (check, remaining) = present h1 (l);
				in 
					if(check) then unordered_equality t1 remaining else false
				end
			fun gcd x 1 = 1 
				|gcd 1 x = 1
				|gcd x y = if(x mod y = 0) then y else if (y mod x = 0) then x else if(x>y) then gcd (x- ((x div y)*y)) y else gcd x (y- ((y div x ) * x))

			fun merge (ICOEFF x, DIV (ICOEFF y),z) (ICOEFF x',DIV (ICOEFF y'),z') = let val cf = gcd y y' in
					(ICOEFF(x+x' + (y div cf) + (y' div cf)), DIV(ICOEFF(y*(y' div cf)) ), z@z')
				end
			fun helper [] = []
				|helper ((hi,hd,hc)::t) = let 
					fun helper2  (hi,hd) [] = (hi,hd,[])
						|helper2 (hi,hd) ((hi',hd',hc')::t) = if(unordered_equality hc hc') then merge (hi',hd',[]) (helper2 (hi,hd) t) 
						else merge (ICOEFF 1, DIV(ICOEFF 1), [(hi',hd',hc')]) (helper2 (hi,hd) t)
					val (ri,rd,rt) = helper2 (hi,hd) t 
					in
						(ri,rd,hc)::(helper rt)
					end
			val reduced_components = helper components

			fun mult_list [] = ICOEFF 1
				|mult_list [x] = x
				|mult_list (h::t) = MULT(mult_list [h] , mult_list t)

			fun one_unit (ICOEFF 1) (DIV (ICOEFF 1)) ps = mult_list ps
				|one_unit (ICOEFF 1) x ps = MULT (x, mult_list ps)
				|one_unit (ICOEFF 0) x ps = ICOEFF 0
				|one_unit x (DIV(ICOEFF 1)) ps = MULT (x, mult_list ps)
				|one_unit x y ps = MULT(x,MULT(y,mult_list ps))

			fun get_sum [] = ICOEFF 0
				|get_sum [(i,d,ps)] = one_unit i d ps
				|get_sum ((i,d,ps)::t) = ADD(one_unit i d ps , get_sum t)
		in
			get_sum reduced_components
		end	

		fun evaluate x (VAR(i)) = let 
			fun pow 1 x = x 
				|pow i x = MULT(x,pow (i-1) x) 
			in
				pow i x 
			end
			|evaluate x (MULT(z,y)) = MULT (evaluate x z, evaluate x y)
			|evaluate x (ADD(y,z)) = ADD(evaluate x y, evaluate x z)
			|evaluate x y = y 

		fun substitute s t (COEFF x)  = if x=s then t else COEFF x
			|substitute s t (ADD (x,z))= ADD(substitute s t x, substitute s t z)
			|substitute s t (MULT(x,y))= MULT(substitute s t x, substitute s t y)
			|substitute s t (DIV x) = DIV(substitute s t x)
			|substitute _ _ x = x

end

