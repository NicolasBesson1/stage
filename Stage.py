

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
N=5
M=7
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


                        
#Input: n the number of variables of the polyhedron, m the number of inequalities defining the polyhedron
#Output: The intersection of the m sets created with polyedre()
def isl_polyhedron(poly):
        isl_poly=formula_to_set(poly[0])
        for i in poly:
                isl_poly=isl_poly.intersect(formula_to_set(i))
        return isl_poly


#Input: An array T containing inequalities
#Output: the conjunction of every inequality
def conjunction(T):
        result=True
        for i in T:
                result=And(result,i)
        return result


def remove_spaces(arr):
        i=0
        while i < len(arr):
                if arr[i]=="" or arr[i]==" ":
                        arr.pop(i)
                i+=1
        return arr





'''
PRINCIPIO
'''

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
        if(operator=="="):
                formula=formula==term
                return formula
        if(operator=="<"):
                return formula<term
        if(operator==">"):
                return formula>term
        if(operator=="and"):
                return And(formula,term)
        if(operator=="or"):
                return Or(formula,term)

#TRue if o is a comparator
def is_comparator(o):
        return o==">=" or o=="<" or o=="<=" or o==">" or o=="="


#True if a string is an operator
def is_operator(o):
        return o=="+" or o=="-" or o=='*'

#True if a string is a logical operator

def is_logical_operator(o):
        return o=="and" or o=="or"

#True if a string contains the name of a variable
def contains_variable(t):
        return "x" in t

def is_int(e):
    k=0
    if(e[0]!='-' and not(ord('0') < ord(e[0]) and ord(e[0]) < ord('9'))):
            return False
    for i in range(1,len(e)):

        if(not(ord('0') < ord(e[i]) and ord(e[i]) < ord('9'))):
                return False
        k+=1
    return True

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
        if(factor =="-"):
                return -1, Int(variable)
        if(factor==""):
                return 1,Int(variable)
        return int(factor),Int(variable)
'''
lexpr -> lexpr lop lexpr
lexpr -> expr cop sexpr
sexpr -> expr cop sexpr
sexpr -> expr
expr -> expr op expr
expr -> INT | VAR
lop -> AND | OR
cop -> > | >= | < | <= | =
op -> + | - | *
'''



def analyse_syntaxique(formule):
    global i
    i=0
    return lexpr(formule)

def lexpr(formule):
        
        expr1=expr(formule)
        c=cop(formule)
        expr2=expr(formule)
        lexpr1=add_to_formula(expr1,c,expr2)

        while(i<len(formule) and is_comparator(formule[i])):
                c=cop(formule)
                expr1=expr2
                expr2=expr(formule)
                lexpr1=add_to_formula(lexpr1,"and",add_to_formula(expr1,c,expr2))

        if(i!=len(formule)):
                l=lop(formule)
                lexpr2=lexpr(formule)
                return add_to_formula(lexpr1,l,lexpr2)
        return lexpr1

def sexpr(formule):
        global i
        expr1=expr(formule)
        return expr1

def expr(formule):
        global i
        
        if(contains_variable(formule[i])):
                a,b=split_variable(formule[i])
                expr1=a*b
        else:
                expr1=int(formule[i])
        i+=1
        while(i<len(formule) and is_operator(formule[i])):
                o=op(formule)
                if(contains_variable(formule[i])):
                        a,b=split_variable(formule[i])
                        expr2=a*b
                else:
                        expr2=int(formule[i])
                i+=1
                expr1=add_to_formula(expr1,o,expr2)
        return expr1

        

def lop(formule):
    global i
    if(i >= len(formule) and not(is_logical_operator(formule[i]))):
        
        print("Erreur syntaxique")
        print(formule)
        print("Index : " + str(i))
        print("Valeur : " + formule[i])
        print("operateur logique attendu")
        quit()
    else:
        i+=1
        return formule[i-1]

def op(formule):
    global i
    i+=1
    return formule[i-1]

def cop(formule):
    global i
    if(i>=len(formule) or not(is_comparator(formule[i]))):
        print("Erreur syntaxique")
        print(formule)
        print("Index : " + str(i))
        print("Valeur : " + formule[i])
        print("comparateur attendu")
        quit()
    i+=1
    return formule[i-1]

'''
FIN
'''

def set_to_formula(bset):
        formula=get_string_context(str(bset))
        formula=formula.split(" ")
        formula=remove_spaces(formula)
        return analyse_syntaxique(formula)
        

#The function creates a random polyhedron, turns it into an ISL set isl_poly, then compares the context of isl_poly
#and the conjunction of every inequality created in the begining.
def test_isl_intersection(n=N,m=M):
        poly=polyedre(n,m)
        isl_poly=isl_polyhedron(poly)
        S=Solver()
        A=conjunction(poly)
        #print(isl_poly)
        B=set_to_formula(isl_poly)
        print(A)
        print(B)
        if(B!=None):
                S.add(Xor(A,B))
                #S.add(Not(Implies(B,A)))
       
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

for i in range(10):
        print(test_isl_intersection())

x=Int("x")
y=Int("y")
A=Or(Not(And((x+3==y),(y>5))),(x>1))

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


