
## Reduce : helper procedure for RowReduction
Reduce := proc(a1, a2, v, d, i, AL)
  # d - orders
  # i - row to reduce
  local j, r, c, a3, la1, la2, L, M1, M0;

  L := OrePoly(0,1);

  la1:=copy(a1);
  la2:=copy(a2);
  r,c:=op(1,a1);
  for j from 1 to r do
    la1[i,j] := 0;
  end do;
  a3:=copy(a2);
  for j from 1 to r do
    if d[j]=0 then
      M1 := map(OrePoly,a3[j]);
      M1 := LinearAlgebra:-Map2(OreTools:-Multiply,L,M1,AL);
      M0 := map(z->`if`(nops(z)>0,op(1,z),0),M1);
      a3[j]:=eval(simplify(M0));
    end if;
  end do;
  la2[i]:=LinearAlgebra:-Transpose(v).a3;
  simplify(la1),simplify(la2);
end proc:


## Row-Reduction algorithm implementation for the first order system
RowReduction := proc(A1::Matrix, A0::Matrix, AL)
  local r, c, i, lc, d, vs, v, j, js, L, la1, la0;

  r,c := op(1,A1);
  if (r<>c) or (op(1,A1)<>op(1,A0)) then
    error "Matrices should be square and of the same dimention";
  end if;

  la1 := copy(A1);
  la0 := copy(A0);

  do
    lc := Matrix(r);
    d := Vector(r);
    for i from 1 to r do
      if LinearAlgebra:-Norm(la1[i])=0 then
        lc[i] := la0[i];
        if LinearAlgebra:-Norm(lc[i]) = 0 then
          error "System is not of full rank";
        end if;
      else
        lc[i] := la1[i];
        d[i] := 1;
      end if;
    end do;

    if LinearAlgebra:-Rank(lc) = r then
      break;
    end if;

    # reduce
    vs := LinearAlgebra:-NullSpace(LinearAlgebra:-Transpose(lc));
    if nops(vs) = 0 then
      error "Something wrong: Rank<r, but dim(NullSpace)=0"
    end if;

    v := vs[1];
    # j = row index to reduce: v[j]<>0, d[j]=max(d[i]: v[i]<>0)
    j := sort([seq([i,d[i]],i=select(i->v[i]<>0, [$1..r]))], (x,y)->x[2]>y[2])[1][1];

    la1,la0 := Reduce(la1, la0, v, d, j, AL);
  end do;

  i := r;
  while (i > 1) and (LinearAlgebra:-Norm(la1[i]) = 0) do
    i := i - 1;
  end do;
  j := 1;
  while j < i do
    if LinearAlgebra:-Norm(la1[j]) = 0 then
      v := la1[i];
      la1[i] := la1[j];
      la1[j] := v;
      v := la0[i];
      la0[i] := la0[j];
      la0[j] := v;
      i := i - 1;
    end if;    
    j := j + 1;
  end do;
  la1, la0;
end proc:


# Extract
# in:
#   A1 - leading matrix
#   A0 - trailing matrix
#   ns - the set of indices of selected unknowns
#   R  - algebra
# out:
#   A   - matrix of normal DES y'=Ay
#   ns1 - the set of pairs <index in initial system, index in A>
#   T   - matrix to obtain selected unknowns that are not be included to A
#   ns2 - the set of pairs <index in initial system, row of T>

Extract := proc(A1::Matrix, A0::Matrix, sel::set, AL)
  local la1, la2, r, c, i, j, k, x, ls, U, L, ll;

  if sel={} then
    ll := {seq(i, i in 1..op(1,A1)[1])};
  else
    ll := sel
  end if;
  la1,la2 := RowReduction(A1,A0,AL);

  # move selected unknowns to begining
  ls := {};
  j := 1;
  for i in sort(ll) do
    if i = j then
      ls := {op(ls), [i, j]};
      j := j + 1;
      next;
    end if;
    x := la1[1..-1,j];
    la1[1..-1,j] := la1[1..-1,i];
    la1[1..-1,i] := x;
    x := la2[1..-1,j];
    la2[1..-1,j] := la2[1..-1,i];
    la2[1..-1,i] := x;
    ls := {op(ls), [i, j]};
    j := j + 1;
  end do;

  k := nops(ls);
  c := 0;

  do
    r,r := op(1,la1);
    j := r;

    #
    while (j > 0) and (LinearAlgebra:-Norm(la1[j]) = 0) do
      for i from k + 1 to r do
        if la2[j,i] <> 0 then
          if i < r then
            x := la1[1..-1,i];
            la1[1..-1,i] := la1[1..-1,r];
            la1[1..-1,r] := x;
            x := la2[1..-1,i];
            la2[1..-1,i] := la2[1..-1,r];
            la2[1..-1,r] := x;
          end if;
          if j < r then
            x := la1[j];
            la1[j] := la1[r];
            la1[r] := x;
            x := la2[j];
            la2[j] := la2[r];
            la2[r] := x;
          end if;

          la2[r,c+1..r] := map(x->`expand`(x/la2[r,r]), la2[r,c+1..r]);
          U := map(OrePoly, Matrix(r-c, shape = identity), 0);
          for i from 1 to r-c - 1 do
            U[i,r-c] := OrePoly(-la2[i+c,r],-la1[i+c,r]);
          end do;

          L := Matrix(r-c, (i,j)->OrePoly(la2[i+c,j+c], la1[i+c,j+c]));
          L := Matrix(r-c, (i,j)->OreTools:-Add(seq(OreTools:-Multiply(U[i,n], L[n,j], AL), n=1..r-c)));

          la2[1+c..r,1+c..r] := map(z->`if`(nops(z)>0,op(1,z),0), L);
          la1[1+c..r,1+c..r] := map(z->`if`(nops(z)>1,op(2,z),0), L);


          r := r - 1;
          break;
        end if
      end do;
      j := j - 1;
    end do;

    #
    if LinearAlgebra:-Norm(la1[r])<>0 then
      if c = 0 then
        return
          [simplify(-(la1[1..r,1..r]^(-1)).la2[1..r,1..r]), ls];
      else
        return
          [simplify(-(la1[1+c..r,1+c..r]^(-1)).la2[1+c..r,1+c..r]),
          {seq([x[1], x[2]-c], x in select(x->x[2]>c, ls))},
          `if`(k>c,
               simplify(la2[1..c,1..c]^(-1).(-la2[1..c,c+1..k])),
               Vector(c)),
          select(x->x[2]<=c, ls)];
      end if;
    end if;

    # SReduce
    c := c + 1;
    for i from c to k do
      if la2[r,i]<>0 then
        if i>c then
          # exchange cols i<->c":
          x := la1[1..-1,i];
          la1[1..-1,i] := la1[1..-1,c];
          la1[1..-1,c] := x;
          x := la2[1..-1,i];
          la2[1..-1,i] := la2[1..-1,c];
          la2[1..-1,c] := x;
          ls := map(x->`if`(x[2]=i,[x[1],c],`if`(x[2]=c,[x[1],i],x)),ls);
        end if;
        la2[r,c..r] := map(x->`expand`(x/la2[r,c]), la2[r,c..r]);

        c := c - 1;
        U := map(OrePoly, Matrix(r-c, (i,j)->`if`(i-1=j,1,0)));
        U[1,r-c]:=OrePoly(1);
        for i from 1 to r-c - 1 do
          U[i+1,r-c] := OrePoly(-la2[c+i,c+1],-la1[c+i,c+1]);
        end do;

        L := Matrix(r-c, (i,j)->OrePoly(la2[i+c,j+c], la1[i+c,j+c]));
        L := Matrix(r-c, (i,j)->OreTools:-Add(seq(OreTools:-Multiply(U[i,n], L[n,j], AL), n=1..r-c)));

        c:=c+1;
        la2[c..r,c..r] := map(z->`if`(nops(z)>0,op(1,z),0), L);
        la1[c..r,c..r] := map(z->`if`(nops(z)>1,op(2,z),0), L);

        break;
      end if;
    end do;

  end do;
end proc:
