"""Independent bivariate generating-function replay and asymptotic holdout."""
import math,json,csv
from research import OUT,append
from ballot import exact_diagonal

def check(p,q,D):
    F=[[0]*(D+1) for _ in range(D+1)];F[0][0]=1
    DP=[[0]*(D+1) for _ in range(D+1)];DP[0][0]=1
    for n in range(1,2*D+1):
        for i in range(max(0,n-D),min(D,n)+1):
            j=n-i;total=0
            for r in range(i+1):
                for s in range(j+1):
                    if r+s and p**r<=q**s:total+=math.comb(r+s,r)*F[i-r][j-s]
            assert total%n==0;F[i][j]=total//n
            if p**i<=q**j:DP[i][j]=(DP[i-1][j] if i else 0)+(DP[i][j-1] if j else 0)
            assert F[i][j]==DP[i][j]
    return (D+1)**2

def main():
    checks=sum(check(p,q,15) for p,q in ((2,3),(2,5),(3,5),(5,7)))
    # Exponent 4096 is withheld from the initial four-pair table.
    exact_diagonal(2,3,4096)
    (OUT/'generating_receipt.json').write_text(json.dumps(dict(independent_integer_coefficients=checks,
        max_bidegree=15,holdout_d=4096),indent=2))
    print('independent generating-function checks complete',checks,flush=True)

if __name__=='__main__':main()
