read "extract.mpl";


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
#   A - list of coefficient matrices
#   dvars - list of unknown functions
#   ivars - independent variable

ODESYSconvert := proc(eqns)
    local sys, ivar, dvars, r, i, A, cur, rem, m, tmp, A1, A0;

    # case of one equation
    if type(eqns, `=`) then
        sys := [eqns];
    else
        sys := convert(eqns,list);
    end if;

    # get single independent variable
    tmp := op(indets(sys,function)[1]);
    if nops([tmp]) = 2 then
        ivar := tmp[2];
    else
        ivar := tmp;
    end if;

    # get list of unknown functions
    dvars := convert(indets(sys, function(identical(ivar))), list);
    
    if (nops(sys) < nops(dvars)) then
    	error "number of equations in system (%1) less than number of unknown functions (%2)", nops(sys), nops(dvars);
	end if;

    A := [];
    r := ODESYSorder(sys);
    rem := -convert(sys, Vector);

    for i from r by -1 to 0 do:
        cur, rem := LinearAlgebra[GenerateMatrix](convert(-rem, list), diff(dvars, [ivar$i]));
        A := [cur, op(A)];
    end do;

    return A, dvars, ivar;
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
    	error "given system is algebraic and therefore can't be converted to first order differential system";
    elif nops(A) = 2 then
    	return A[2], A[1];
    end if;

    r := nops(A)-1;
    m := op(A[1])[1];

    # construct A1
    A1 := Matrix(r*m, r*m, (i,j)->`if`(i=j, 1, 0));
    # assign bottom right m*m submatrix to A_r
    A1[(r-1)*m+1 .. r*m, (r-1)*m+1 .. r*m] := A[-1];

    # construct A0
    A0 := < Matrix((r-1)*m, r*m, (i,j)->`if`(j=i+m, -1, 0)), Matrix(A[1..-2]) >;
    
    return A1, A0;
end proc;



# ExtrAB
# in:
#   eqns - a set or a list of ODEs of initial system
#   ns - set of names of selected unknowns
#   R  - algebra
# out:
#   resDif - list of ODEs of new differential system
#   resAlg - list of algebraic equations that are expressing how
#              to obtain selected unknowns that aren't included in resDif

ExtrAB := proc(eqns, ns, R := OreTools:-SetOreRing(x, 'differential'))
    local A, dvars, ivar, A1, A0, i, j, ns1, ns2, indsInInit, indsInNew, M, extrRes, abRes, tmp, curSum, tmp2, resVars, resDif, resAlg;

    if type(eqns[1],Matrix) then
        
        A1, A0 := eqns[1], eqns[2];

        ns1 := ns;
        ivar := x;
        dvars := {};
        for i from 1 to op(eqns[1])[1] do
            dvars := {op(dvars), (y||i)(x)};
        end do;
    else
        A, dvars, ivar := ODESYSconvert(eqns);

        A1, A0 := ODESYSordreduce(A);

        # fill the set of indices of selected unknowns
        ns1 := {};
        for i from 1 to nops(dvars) do
            if dvars[i] in ns then
                ns1 := {op(ns1),i};
            end if;
        end do;

    end if;

    #print(A1, A0);
    if LinearAlgebra[Determinant](A1) <> 0 then
    	M := -A1^(-1).A0;
        ns2 := ns1;
    else
        # apply Extract

    	extrRes := Extract(A1, A0, ns1, R);

    	M := extrRes[1];

    	# get indices of selected vars in new syst
        indsInInit := map(pair->op(1,pair), extrRes[2]);
        indsInNew := map(pair->op(2,pair), extrRes[2]);
    	ns2 := convert(indsInNew, set);
    end if;


    if not assigned(extrRes) then
        indsInInit := convert(ns1, list);
    elif nops(extrRes) = 4 then
        resAlg := [];
        for i from 1 to nops(extrRes[4]) do
            curSum := 0;
            for j from 1 to nops(extrRes[2]) do
                curSum := curSum + extrRes[3][i,j]*dvars[indsInInit[j]]
            end do;
            resAlg := [op(resAlg), dvars[extrRes[4][i][1]]=curSum];
        end do;

    end if;

    # apply AB-algorithm

    # M := Matrix([[0,0,0,1,0,0],[0,0,0,0,1,0],[0,0,0,0,0,1],[-2/3,0,0,-1/3,-4/3,0],[0,-5,0,0,0,0],[0,0,-1,0,0,0]]);

	abRes := OreTools:-Consequences:-ReducedSystem(M, ns2, R);


    tmp := [];
    for i from 1 to nops(abRes[2])-1 do
        tmp := [op(tmp), abRes[2][i+1][2]-abRes[2][i][2]-1];
    end do;
    tmp := [op(tmp), op(1,abRes[1])[1]-abRes[2][-1][2]];


    # list of unknowns of the resulting system
    resVars := [];
    for i from 1 to nops(indsInInit) do
        for j from 0 to tmp[i] do
            resVars := [op(resVars), diff(dvars[indsInInit[i]], [ivar$j])]
        end do;
    end do;


    resDif := [];
    for i from 1 to nops(resVars) do
        curSum := 0;
        for j from 1 to nops(resVars) do
            curSum := curSum + resVars[j]*abRes[1][i,j];
        end do;

        if curSum <> diff(resVars[i], ivar) then
            resDif := [op(resDif), diff(resVars[i], ivar)=curSum];
        end if
    end do;


    if assigned(resAlg) then
        return resDif, resAlg;
    else
        return resDif;
    end if;
end proc;