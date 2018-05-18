read "extractp.mpl";


# ODESYSorder
# in:
#   eqns - System of ODEs
# out:
#   n - order of the ODEs system

ODESYSorder := proc(eqns)
    return max(map(PDEtools[difforder], eqns));
end proc;



# ODESYSconvert
# in:
#   eqns - System of ODEs
# out:
#   A - list of coefficients matrices
#   F - vector-column of right parts

ODESYSconvert := proc(eqns)
    local sys, ivar, dvars, r, i, A, cur, rem, m, tmp, A1, A0;

    # case of one equation
    if type(eqns, `=`) then
        sys := [eqns];
    else
        sys := convert(eqns,list);
    end if;

    tmp := op(indets(sys,function)[1]);
    if nops([tmp]) = 2 then
        ivar := tmp[2];
    else
        ivar := tmp;
    end if;

    dvars := convert(indets(sys, function(identical(ivar))), list);

    A := [];
    r := ODESYSorder(sys);
    rem := -convert(sys, Vector);

    for i from r by -1 to 0 do:
        cur, rem := LinearAlgebra[GenerateMatrix](convert(-rem, list), diff(dvars, [ivar$i]));
        A := [op(A), cur];
    end do;

    return A;
end proc;



# ODESYSordreduce
# in:
#   A - list of coefficients matices
# out:
#   A1 - leading matrix
#   A0 - trailing matrix

ODESYSordreduce := proc(A::list)
    local r, m, A1, A0;

    if nops(A) < 2 then
    	error;
    elif nops(A) = 2 then
    	return A[1], A[2];
    end if;

    r := nops(A)-1;
    m := op(A[1])[1];

    # construct A1
    A1 := Matrix(r*m, r*m, (i,j)->`if`(i=j, 1, 0));
    A1[(r-1)*m+1 .. r*m, (r-1)*m+1 .. r*m] := A[1]; # assign bottom right m*m submatrix to A[r]

    # construct A0
    A0 := < Matrix((r-1)*m, r*m, (i,j)->`if`(j=i+m, -1, 0)), Matrix(ListTools[Reverse](A[2..-1])) >;
    
    return A1, A0;
end proc;



# ExtrAB
# in:
#   eqns - a single ODE or a set or list of ODEs
#   ns - set or list of indices of selected unknowns
# out:
#   res - 
#   ns1 - the set of pairs <index in initial system, index in A>

ExtrAB := proc(eqns, ns)
    local A, A1, A0;

    A := ODESYSconvert(eqns);

    A1, A0 := ODESYSordreduce(A);

    if LinearAlgebra[Determinant](A1) = 0 then
    	
    end if;

    return 1;
end proc;