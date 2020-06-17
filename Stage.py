

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
N=7
M=12
#Renvoit une liste d'inegalites en Z3 correspondant a un polyedre convexe
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

'''L'objective de toutes les fonctions qui suivent c'est de
generer un polyedre en Z3 avec la fonction precedente, transformer chaque formule
definissant le polyedre en un ensemble ISL, et calculer leur intersection.
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
        return BasicSet( "{ ["+arguments+"] : " + str(formula) + "}" )


#Input: basic set
#Output: context of the set in string format
def get_string_context(bset):
        strbset = str(bset)
        result=""
        copy=False
        #What's between ":" and "}" (i.e. the context) will be stored in "result"
        for i in strbset:
                if(i=="}"):
                        copy=False
                if(copy):
                        result+=i
                if(i==":"):
                        copy=True
        return result

#Returns the operation: formula operator term
def add_to_formula(formula, operator, term):
        if(operator=="+"):
                formula = formula + term
                return formula 
        if(operator=="-"):
                formula-=term
                return formula
        if(operator=="*"):
                formula*=term
                return formula
        if(operator=="<="):
                formula = formula<=term
                return formula
        if(operator==">="):
                formula=formula>=term
                return formula
        if(operator=="=="):
                formula=formula==term
                return formula
        if(operator=="<"):
                return formula<term
        if(operator==">"):
                return formula>term

#TRue if o is a comparator
def is_comparator(o):
        return o==">=" or o=="<" or o=="<=" or o==">"


#True if a string is an operator
def is_operator(o):
        return o=="+" or o=="-"

#True if a string contains the name of a variable
def contains_variable(t):
        return "x" in t


#Input: a string nxi, with n an and i integers
#Output: the tubple int(n),Int(xi)
def split_variable(t):
        factor=""
        variable=""
        xfound=False
        for i in t:
                if i=="x":
                        xfound=True
                if xfound:
                        variable+=i
                else:
                        factor+=i
        if(factor==""):
                return 0,Int(variable)
        return int(factor),Int(variable)

#Input: an ISL basic set
#Output: the Z3 formula that defines the set (the context)
def set_to_formula(bset):
        result=0
        context=get_string_context(bset)
        arr=context.split(" ")
        operator=""
        comparator=""
        for i in arr:
                
                if is_comparator(i):
                        comparator=i
                        left=result
                        result=0
                elif is_operator(i):
                        operator=i  
                elif contains_variable(i):
                        a,b=split_variable(i)
                        if operator!="":
                                result=add_to_formula(result,operator,a*b)
                        else:
                                result=a*b
                elif len(i)!=0:
                        if operator!="":
                                result=add_to_formula(result,operator,Int(i))
                        else:
                                result=int(i)
                
        return add_to_formula(left,comparator,result)

                        
#Input: n the number of variables of the polyhedron, m the number of inequalities defining the polyhedron
#Output: The intersection of the m sets created with polyedre()
def isl_polyhedron(n=7,m=14):
        poly=polyedre(n,m)
        isl_poly=formula_to_set(poly[0])
        for i in poly:
                isl_poly.intersect(formula_to_set(i))
        return isl_poly

print(isl_polyhedron())

