

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
N=2
M=4
i=0
#Renvoit une liste d'inegalites en Z3 correspondant a un polyedre convexe
def polyedre(n=N,m=M):
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
                A=[[randint(-100,100) for i in range(n)] for j in range(m)]
                #X est l'ensemble des variables
                X=[Int("x"+str(i)) for i in range(n)]
                #B correspond aux membres de droite de chaque inegalite
                B=[randint(-100,100) for i in range(m)]
                polyedre=[]
                

                for i in range(len(A)):
                        #Termes contient le membre de gauche de l'inegalite:
                        
                        termes=[]
                        for j in range(len(X)):
                                termes+=[A[i][j]*X[j]]


                        #On ajoute a S l'inegalite:
                        # sum(A[i][j]*X[j]) <= B[i]
                        S.add(sum(termes)<=B[i])
                        polyedre.append(sum(termes)<=B[i])
                #print(S.check()==sat)
                '''for x in X:
                        S.add(x>=0)
                        polyedre.append(x>=0)'''
                satisfaisable=S.check()==sat
        #print(S.check())

        return polyedre

poly=polyedre(n=N,m=M)



#Test ISL
'''
space = Space.create_from_names(DEFAULT_CONTEXT, set=["x", "y"])

bset = (BasicSet.universe(space)
        .add_constraint(Constraint.ineq_from_names(space, {1: -1, "x": 1}))
        .add_constraint(Constraint.ineq_from_names(space, {1: 5, "x": -1}))
        .add_constraint(Constraint.ineq_from_names(space, {1: -1, "y": 1}))
        .add_constraint(Constraint.ineq_from_names(space, {1: 5, "y": -1})))
print("set 1 %s:" % bset)

bset2 = BasicSet("{[x, y] : x >= 0 and x < 5 and y >= 0 and y < x+4 }")
print("set 2: %s" % bset2)

bsets_in_union = []
bset.union(bset2).convex_hull().foreach_basic_set(bsets_in_union.append)
print(bsets_in_union)
union, = bsets_in_union
print("union: %s" % union)

'''


'''L'objectif de toutes les fonctions qui suivent c'est de
generer un polyedre en Z3 avec la fonction precedente, transformer chaque formule
definissant le polyedre en un ensemble ISL, et calculer leur intersection.
Ensuite, nous allons prendre la formule definissant l'ensemble obtenu,
pour voir si elle est equivalente a la conjonction de toutes les formules Z3 generees
originalement
'''

#Input: a list of strings
#Output: a string corresponding to the concatanation of al the strings in the list
def concat(T):
        result = ""
        for i in T:
                result+=i
        return result

#bset=BasicSet("{[x0,x1,x2,x3] : " + str(poly[0]) + "}")
#print(bset)


#Input: a Z3 formula
#Output: an ISL set defined by the formula
def formula_to_set(formula):
        #Assuming the variables in "formula" have the format x0,x1, ... xN
        arguments = concat( [concat(["x",str(i),","]) for i in range(N-1) ]) + str("x") + str(N-1)
        return Set("{ ["+arguments+"] : " + str(formula) + "}" )


                        
#Input: n the number of variables of the polyhedron, m the number of inequalities defining the polyhedron
#Output: The intersection of the m sets created with polyedre()
def isl_intersection(poly):
        isl_poly=formula_to_set(poly[0])
        for i in poly:
                isl_poly=isl_poly.intersect(formula_to_set(i))
        return isl_poly

def isl_union(poly):
        isl_poly=formula_to_set(poly[0])
        for i in poly:
                isl_poly=isl_poly.union(formula_to_set(i))
        return isl_poly


#Input: An array T containing inequalities
#Output: the conjunction of every inequality
def conjunction(T):
        result=True
        for i in T:
                result=And(result,i)
        return result

def disjunction(T):
        result=False
        for i in T:
                result=Or(result,i)
        return result



def islf_to_z3f(constraint):
        d=constraint.get_coefficients_by_name()
        formula=0
        for i in d:
                if(type(i)==str):
                        formula += Int(i)*d[i].to_python()
                else:
                        formula += d[i].to_python()
        if(constraint.is_div_constraint()):
                
                return 0
        return formula >= 0


def isl_to_z3(set):
        bsets=set.get_basic_sets()
        result=False
        for bset in bsets:
                constraints=bset.get_constraints()
                t=True
                for constraint in constraints:
                        t = And(t,islf_to_z3f(constraint))
                result=Or(result,t)
        return result

#The function creates a random polyhedron, turns it into an ISL set isl_poly, then compares the context of isl_poly
#and the conjunction of every inequality created in the begining.

def test_isl_intersection(n=N,m=M):
        poly=polyedre(n,m)
        isl_poly=isl_intersection(poly)
        S=Solver()
        A=conjunction(poly)
        #print(isl_poly)
        B=isl_to_z3(isl_poly)
        if(B!=None):
                S.add(Xor(A,B))
                #S.add(Not(Implies(B,A)))
       
        result=S.check()
        return result==unsat

def test_isl_union(n=N,m=M):
        poly=polyedre(n,m)
        isl_poly=isl_union(poly)
        S=Solver()
        A=disjunction(poly)
        #print(isl_poly)
        B=isl_to_z3(isl_poly)
        if(B!=None):
                S.add(Xor(A,B))
        result=S.check()
        return result==unsat
        
'''
S=Solver()
#-6x0+3x1<=1 and 2*x0+7x1<=1
A=And(-6*Int("x0")+3*Int("x1")<=1, 2*Int("x0")+7*Int("x1")<=1)
#x1>-2x0
B=Int("x1")<=2*Int("x0")
S.add(Not(Implies(A,B)))

print(S.check())
m=S.model()


for d in m.decls():
    print ("%s = %s" % (d.name(), m[d]))
'''

ex=polyedre()
exi=isl_union(ex)

print(exi.get_basic_sets())

'''
for i in range(100):
        print(test_isl_union())'''




'''
x=Int("x")
y=Int("y")
A=Or(Not(And((x+3==y),(y>5))),(x>1))

poly=polyedre()
S=isl_union(poly)
print(S)

print(S.get_basic_sets()[5].get_constraints()[0])
print(S.get_basic_sets()[5].get_constraints()[0].get_coefficients_by_name(3))
'''

'''Methode de cooper:
-formule=Tactic("nnf")(formule).as_expr()
-simplify(formule,eq2ineq)

A=Tactic("nnf")(A).as_expr()


substitute(A,(x,Int("z")+1))

print(A)

a=Int("a")
b=Int("b")


print(A)

help_simplify()
lol=BasicSet("{ [x] : x=1}")

'''


