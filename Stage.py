from z3 import *
from random import randint
from islpy import *

'''
#Test de z3
S2=Solver()
x,y=Int("x"),Int("y")
S2.add(x+5==y)
S2.add(y<=23)
S2.add(x>17)
print(S2.check())
'''
#Global constants
N,M=7,14
def polyedre(n=3,m=3):
        satisfaisable=False

        # Tant que l'ensemble n'est pas satisfaisable
        # donc tant que le polyedre soit vide
        while(not(satisfaisable)):
        #Declaration de variables
                S=Solver()
                #A est une matrice de n*m, X est un vecteur de dimension n et B de m
                #n est le nombre d'inconnues du systeme d'innequations
                #m est le nombre d'inegalites du systeme
                #A[i] correspond aux coefficients des variables a l'inegalite i
                A=[[randint(-10,10) for i in range(n)] for j in range(m)]
                #X est l'ensemble des variables
                X=[Int("x"+str(i)) for i in range(n)]
                #B correspond aux membres de droite de chaque inegalite
                B=[randint(-10,10) for i in range(m)]
                polyedre=[]
                print(A)
                print(B)

                for i in range(len(A)):
                        #Termes contient le membre de gauche de l'inegalite:
                        
                        termes=[]
                        for j in range(len(X)):
                                termes+=[A[i][j]*X[j]]

                        #On ajoute a S l'inegalite:
                        # sum(A[i][j]*X[j]) <= B[i]
                        S.add(sum(termes)<=B[i])
                        polyedre.append(sum(termes)<=B[i])
                print(S.check()==sat)
                satisfaisable=S.check()==sat
        print(S.check())
        return polyedre
poly=polyedre(n=N,m=M)

def formula_to_set(formula):
        #Assuming the variables in "formula" have the format x0,x1, ... xN
        print(formula)
        
        arguments = concat( [concat(["x",str(i),","]) for i in range(N-1) ]) + str("x") + str(N-1)

        print(arguments)
        return BasicSet( "{ ["+arguments+"] : " + str(formula) + "}" )

print(formula_to_set(poly[0]))

'''
#Test ISL
space = isl.Space.create_from_names(isl.DEFAULT_CONTEXT, set=["x", "y"])

bset = (isl.BasicSet.universe(space)
        .add_constraint(isl.Constraint.ineq_from_names(space, {1: -1, "x": 1}))
        .add_constraint(isl.Constraint.ineq_from_names(space, {1: 5, "x": -1}))
        .add_constraint(isl.Constraint.ineq_from_names(space, {1: -1, "y": 1}))
        .add_constraint(isl.Constraint.ineq_from_names(space, {1: 5, "y": -1})))
print("set 1 %s:" % bset)

bset2 = isl.BasicSet("{[x, y] : x >= 0 and x < 5 and y >= 0 and y < x+4 }")
print("set 2: %s" % bset2)

bsets_in_union = []
bset.union(bset2).convex_hull().foreach_basic_set(bsets_in_union.append)
print(bsets_in_union)
union, = bsets_in_union
print("union: %s" % union)
'''
