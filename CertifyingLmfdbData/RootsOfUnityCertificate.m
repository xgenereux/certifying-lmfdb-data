/* Given an absolute number field K, we return a certificate for the torsion units.

   Format of the certificate:
   
   - Order of torsion unit group
   - Generator, as an element of the number field
   - A list of primes such that the mod-p-reduction gives a sharp upper bound.
     The entries in the list have the format:
     <p, #(O_K / P)^\times, Generators of the ideal P>
     with P and ideal above p.
   - A ZZ-Basis of the maximal order. 

   We use only p with p-1 > [K:Q]. This way there is no p-torsion in the
   unit group and therefore, the mod P reduction is injective on the torsion
   units. Further, we use only unramified primes.                               
   
   The Chebotarev density theorem implies that a certificate of the above
   shape always exists.
   
    */

function TorsionUnitsCertificate(K)
 assert IsAbsoluteField(K);
 
 ord := MaximalOrder(K);
 di := Discriminant(ord);
 u1,u2 := TorsionUnitGroup(ord);
 gen := K!u2(u1.1);
 p := NextPrime(Degree(K)+2); 
 while di mod p eq 0 do p := NextPrime(p); end while;

 PrimesUsed := []; 
 fac := Factorization(p*ord);
 qs := Norm(fac[1][1])-1;
 Append(~PrimesUsed, <p, qs, [K!a : a in Generators(fac[1][1])]>);
/* left is the list of all primes p such that the p-Sylow-Subgroup
   of u1 is smaller than the current upper bound.                     */ 
 left := [a : a in PrimeDivisors(qs) | Valuation(qs,a) ne Valuation(#u1,a)];   

/* Now we extend the list of used primes. Each new prime in the list 
   has to eliminate at least one prime in the list left.              */
 while #left gt 0 do
   p := NextPrime(p);
   while di mod p eq 0 do p := NextPrime(p); end while;  
   fac := Factorization(p*ord);
   qs := Norm(fac[1][1])-1;
   if &or [Valuation(qs,a) eq Valuation(#u1,a) : a in left] then
     left := [a : a in left | Valuation(qs,a) ne Valuation(#u1,a)];
     Append(~PrimesUsed, <p, qs, [K!a : a in Generators(fac[1][1])]>);
   end if; 
 end while;

// Minimising the certificate:
 k := 1;
 while k le #PrimesUsed and #PrimesUsed gt 1 do
   if Gcd([PrimesUsed[i][2] : i in [1..#PrimesUsed] | i ne k]) eq #u1 then
     Remove(~PrimesUsed,k);
   else
     k := k + 1;   
  end if;
 end while;
 
 return #u1, gen, PrimesUsed, [K!a : a in Basis(ord)];
end function;

/* Test examples */
q<x> := PolynomialRing(Rationals());
nf := CompositeFields(CyclotomicField(7), NumberField(x^3+x+11))[1];
TorsionUnitsCertificate(nf);


for d := -20 to 20 do
 if IsFundamentalDiscriminant(d) then
  d;
  K := QuadraticField(d);
  TorsionUnitsCertificate(K);
  "--------------------";
 end if;
end for;


