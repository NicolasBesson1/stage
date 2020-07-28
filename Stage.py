from z3 import *
from islpy import *
from random import randint


#Input: a list of strings
#Output: a string corresponding to the concatanation of al the strings in the list
def concat(T):
        result = ""
        for i in T:
                result+=i
        return result



#Input: a string nei or (nei), with n and i two integers
#Output: the tuple int(n),Int("ei")
def split_variable(t):
        factor=""
        variable=""
        xfound=False
        for i in t:
                if i=="e":
                        xfound=True
                if xfound:
                        if i!=")":
                                variable+=i
                else:
                        if i!="(":
                                factor+=i                        
        if(factor =="-"):
                return -1, Int(variable)
        if(factor==""):
                return 1,Int(variable)
        return int(factor),Int(variable)


#True if a string contains the name of a variable (la convention sur ISL c'est Exists e0, e1 ... en: P(e0,e1, ..., en))
def contains_variable(t):
        return "e" in t


#N le nombre de variables
#M le nombre d'inéquations définissant le polyhedre

N=2
M=2

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




#Input: An array T containing formulas
#Output: the conjunction of every formula
def conjunction(T):
        if(len(T)>0):
                result=T[0]
                for i in T[1:]:
                        result=And(result,i)
                return result
        return True

#Input: An array T containing formulas
#Output: the disjunction of every formula
def disjunction(T):
        if(len(T)>0):
                result=T[0]
                for i in T[1:]:
                        result=Or(result,i)
                return result
        return True

#Input: basic set
#Output: context of the set in string format
def get_string_constraint(c):
        str_c = str(c)
        result=""
        copy=False
        #What's between ":" and "}" (i.e. the constraint) will be stored in "result"
        for i in str_c:
                if(i=="}"):
                        copy=False
                if(copy):
                        result+=i
                if(i==":"):
                        copy=True
        return result

#Remove spaces and empty strings from an array of strings
def remove_spaces(arr):
        i=0
        while i < len(arr):
                if arr[i]=="" or arr[i]==" ":
                        arr.pop(i)
                i+=1
        return arr

#Returns true if  the string e is an integer
def is_int(e):
    k=0
    if(e[0]!='-' and not(ord('0') < ord(e[0]) and ord(e[0]) < ord('9'))):
            return False
    for i in range(1,len(e)):
        if(not(ord('0') < ord(e[i]) and ord(e[i]) < ord('9'))):
                return False
        k+=1
    return True

#Input: a string with the format: "n*floor(var/n)"
#Output: int(n)
def get_denominator(e):
    result=""
    i=0
    while ord(e[i]) <= ord('9') and ord(e[i]) >= ord('0'):
        result+=e[i]
        i+=1
    return int(result)


#Input: a string with the format: "-x" or "x"
#Output: Int("x")
def get_var(e):
    if(e[0]=="-"):
        return Int(e[1:])
    return Int(e)


#Input: an ISL constraint
#Output: a z3 formula equivalent to the constraint
#A non divisibility constraint is defined with a dictionnary:
# x0: v0
#...
# xn: vn
# 1 : v
# The keys are the names of the variables (except for the key "1", corresponding to the constant)
# The value of the key xi is the coefficient of the variable
# The value of the key 1 is the constant.
#The formula associated is: v0x0 + ... + vnxn + v >= 0 if c is not an equality (else the >= has to be replaced with an ==)
def islconstraint_to_z3_constraint(c):
        z3_c=0
        coefficients=c.get_coefficients_by_name()
        for var in coefficients:
                if(type(var)==str):
                        z3_c += Int(var)*coefficients[var].to_python()
                else:
                        z3_c += var*coefficients[var].to_python()
        if(c.is_equality()):
                return z3_c==0
        return z3_c>=0
        

#Input: an ISL divisibility constraint or an exists constraint 
#Output: a z3 formula equivalent to the constraint

def isldivconstraint_to_z3divconstraint(c):

        str_c=get_string_constraint(c)
        arr_c=remove_spaces(str_c.split(" "))
        if arr_c[0] != "exists":
                if(is_int(arr_c[0])):
                        x=Int(arr_c[2])
                        q=get_denominator(arr_c[4])
                        return Not(x%q==0)
                else:
                        x=get_var(arr_c[0])
                        q=get_denominator(arr_c[2])
                return x%q==0
        z3_c=0
        coefficients=c.get_coefficients_by_name()
        for var in coefficients:
                if(type(var)==str):
                        z3_c += Int(var)*coefficients[var].to_python()
                else:
                        z3_c += var*coefficients[var].to_python()

        #Dans le tableau ["exists", "e0,", ... , "en:", ... ]
        #on cherche l'indice a partir duquel la formule est presente
        i=0
        while(arr_c[i][len(arr_c[i])-1] != ":"):
                i+=1
        i+=1
        
        for j in range(i,len(arr_c[i:])):
                if contains_variable(arr_c[j]):
                        a,e=split_variable(arr_c[j])
                        
                        if arr_c[j-1] == "-":
                                z3_c += -a*e
                        else:
                                z3_c += a*e

        return z3_c >= 0

#With get_string_constraint we can get the string of the formula defining the set.
#If the first element of the string is "exists" or "(exists" then we know the definition
#of the set contains an exists quantifier
def is_exists_isl(S):
        str_c=get_string_constraint(S)
        arr_c=remove_spaces(str_c.split(" "))
        if(len(arr_c)>0):
                return arr_c[0]=="(exists" or arr_c[0]=="exists"
        return False

#Get variable allows to get the z3 variable ei, in 'Exists e0, ..., ei , ..., en: P(e0, ... en)'
def get_variable(s):
        r="e"
        i=0
        while s[i]!="e":
                i+=1
        i+=1
        while ord(s[i]) <= ord("9") and ord(s[i]) >= ord("0"):
                r+=s[i]
                i+=1
        return Int(r)

#Input: a set defined with the formula: 'Exists e0, ..., en: P(e0, ... en)'
#Output: An array with the z3 variables e0, ..., en
#This is done casting the set to a string and reading the string
def get_variables(S):
        str_c=get_string_constraint(S)
        arr_c=remove_spaces(str_c.split(" "))
        i=1
        Variables=[]
        while(arr_c[i][len(arr_c[i])-1] != ":"):
                Variables.append(get_variable(arr_c[i]))
                i+=1
        Variables.append(get_variable(arr_c[i]))
        return Variables
#Input: ISL set
#Output: Z3 formula. The output corresponds to the formula defining the ISL set
#Conditions:
#       -If the set is defined with an "exists" quantifier, it only works when there is one unique basic set and there are no divisibility constraints
#     
def isl_to_z3(S):

        #The set S is the union of the basic sets returned by S.get_basic_sets()
        bsets=S.get_basic_sets()
        z3_bsets=[]
        

        for bset in bsets:
                #The basic set bset is the intersection of all the constraints returned by bset.get_constraints()
                C=bset.get_constraints()
                z3_C=[]
                for c in C:
            
                        #If the constraint is not a divisibility constraint, it has the form aX>=0 
                        if(not(c.involves_dims(dim_type.div,first=0,n=bset.dim(4)))):
                                z3_C.append(islconstraint_to_z3_constraint(c))
                        #Else: it has the form a%q=0 or not(a%q=0)
                        else:
                                z3_c=isldivconstraint_to_z3divconstraint(c)
                                if(z3_c not in z3_C):
                                        z3_C.append(z3_c)

                if(z3_C not in z3_bsets):
                        z3_bsets.append(z3_C)

        formula=disjunction([conjunction(b) for b in z3_bsets])

        if(is_exists_isl(bset)):
                Variables=get_variables(bset)
                for i in range(len(Variables)):
                        formula=Exists(Variables[len(Variables)-i-1],formula)
        return formula
            


#Input: a Z3 formula
#Output: an ISL set defined by the formula
def formula_to_set(formula):
        #Assuming the variables in "formula" have the format x0,x1, ... xN
        arguments = concat( [concat(["x",str(i),","]) for i in range(N-1) ]) + str("x") + str(N-1)
        return Set("{ ["+arguments+"] : " + str(formula) + "}" )

#Input: poly is an array with z3 inequalities
#Output: The intersection of the m sets created with polyedre()
def isl_intersection(poly):
        isl_poly=formula_to_set(poly[0])
        for i in poly:
                isl_poly=isl_poly.intersect(formula_to_set(i))
        return isl_poly

#Input: poly is a set of z3 inequalities
#Output: The union of the m sets created with polyedre()
def isl_union(poly):
        isl_poly=formula_to_set(poly[0])
        for i in poly:
                isl_poly=isl_poly.union(formula_to_set(i))
        return isl_poly


#Input: poly is a set of z3 inequalities
#Output: Once the intersection of every inequality is computed, we project the set into the x axis, we return the resulting set
def isl_projection(poly,x):
    S=isl_intersection(poly)
    return S.project_out(dim_type.out,first=x,n=1)

#Creates a set of inequalities, A is the conjunction of all the inequalities.
#isl_poly is the intersection of the sets defined by each inequality in poly
#B is the formula defining isl_poly
#Returns Xor(A,B)==unsat
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

#Creates a set of inequalities, A is the disjunction of all the inequalities.
#isl_poly is the union of the sets defined by each inequality in poly
#B is the formula defining isl_poly
#Returns Xor(A,B)==unsat
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
               
#Creates a set of inequalities, A is the formula: exists x, conjunction(poly) 
#isl_poly is the projection on the x axis of the intersection of every set defined by one inequality
#B is the formula defining isl_poly
#Returns Xor(A,B)==unsat
#When there are more than 2 variables, there seems to be an infinite loop when the set is defined with an exists quantifier
def test_isl_projection(n=N,m=M):
        poly=polyedre(n,m)
        x=randint(0,n-1)
        isl_poly=isl_projection(poly,x)

        A=Exists(Int("x"+str(x)),conjunction(poly))
        B=isl_to_z3(isl_poly)

        S=Solver()
        if(B!=None):
                S.add(Xor(A,B))
        print(A)
        print(B)
        result=S.check()
        return result==unsat

    

'''print(isl_to_z3(PS1))
print(PS1)'''
#print(isl_to_z3(S))

for i in range(10):
        print(test_isl_projection())
        
