from z3 import *

from random import randint


'''
#Test de z3
S2=Solver()
x,y=Int("x"),Int("y")

S2.add(x+5==y)
S2.add(y<=23)
S2.add(x>17)
print(S2.check())
'''
satisfaisable=False

# Tant que l'ensemble n'est pas satisfaisable
# donc tant que le polyedre soit vide
while(not(satisfaisable)):
    #Declaration de variables
    S=Solver()
    #A est une matrice de n*m, X est un vecteur de dimension n et B de m
    #n est le nombre d'inconnues du systeme d'innequations
    n=randint(10,12)
    #m est le nombre d'inegalites du systeme
    m=randint(10,12)
    #A[i] correspond aux coefficients des variables a l'inegalite i
    A=[[randint(-10,10) for i in range(n)] for j in range(m)]
    #X est l'ensemble des variables
    X=[Int("x"+str(i)) for i in range(n)]
    #B correspond aux membres de droite de chaque inegalite
    B=[randint(-10,10) for i in range(m)]


    for i in range(len(A)):
        #Termes contient le membre de gauche de l'inegalite:
        
        termes=[]
        for j in range(len(X)):
            termes+=[A[i][j]*X[j]]

        #On ajoute a S l'inegalite:
        # sum(A[i][j]*X[j]) <= B[i]
        S.add(sum(termes)<=B[i])
    
    satisfaisable=S.check()==sat
    
def is_exists(S):
    return S.split(" ")[0]=="(exists"

'''METHODE DE COOPER'''
def step1(F):
        #Mettre F en nnf
        if(is_exists(F.sexpr())):
            
            return Exists(Int(F.var_name(0)),Tactic("nnf")(F.body()).as_expr())
        return Tactic("nnf")(F).as_expr()
                    


def gerer_egalite(F):
        #Si F est a%q==r on renvoit a-r%q==0
        #Sinon on renvoit And(A<B+1, B<A+1)
        children=F.children()
        A=children[0]
        B=children[1]      
        if(is_mod(A)):
            grand_children=A.children()
            a=grand_children[0]
            q=grand_children[1]
            r=B
            return (a-r % q) == 0
        if(is_mod(B)):
            grand_children=B.children()
            a=grand_children[0]
            q=grand_children[1]
            r=A
            return (a-r % q) == 0
        return And(A<B+1,B<A+1)
        



def step2(F):
    if(type(F)==bool or type(F)==int or is_var(F) or is_const(F)):
        return F
    children=F.children()
    #Si F = Exists(x,F'(x)), on applique la methode de cooper sur F.
    if(is_exists(F.sexpr())):
        return methode_cooper(F)
    #Si F est une formule de la forme Not(...)
    if(is_not(F)):
        grand_children=children[0].children()
        A,B=grand_children[0],grand_children[1]
        if(is_eq(children[0])):
            # Si F est de la forme Not(A%B==0) on laisse la formule telle qu'elle est
            if(is_mod(A) or is_mod(B)):
                return Not(children[0])
            #Si F est de la forme Not(A==B) on transforme pour avoir A<B ou B<A
            return Or(A<B,B<A)
        #Si F est de la forme Not(A<B) on renvoit B < A+1
        if(is_lt(children[0])):
            return B<A+1
        #Idem pour le reste
        if(is_gt(children[0])):
            return A<B+1
        if(is_le(children[0])):
            return A>B
        if(is_ge(children[0])):
            return A<B
    if(is_eq(F)):
        #Si F est a%q==r on renvoit a-r%q==0
        #Sinon on renvoit And(A<B+1, B<A+1)
        return gerer_egalite(F)
    if(is_le(F)):
        return A<B+1
    if(is_ge(F)):
        return B<A+1
    #Si F est de la forme And/Or(F1,F2, ... Fn) on renvoit And/Or(step2(F1),...,step2(Fn))
    if(is_and(F) or is_or(F)):
        result=step2(children[0])
        for i in children[1:]:
            result=F.decl()(result,step2(i))
            
    return False
            
            

def sum_coefficients(F,x):

    children=F.children()
    if(eq(x,F)):
        return 1
 
    if(len(children)==0 or len(children)==1 or len(children)>2):
        return 0
    
    if(str(F.decl())=="*"):
        if(eq(children[0],x)):
            return children[1]
        elif(eq(children[1],x)):
            return children[0]
        else:
            return 0  
    
    if(str(F.decl())=="+"):
        return sum_coefficients(children[0],x)+sum_coefficients(children[1],x)
    return 0


def contains_x(F,x):
    children=F.children()
    if(len(children)==0):
        return eq(F,x)

    result=False
    for i in children:
        result=result or contains_x(i,x)
    return result
    
    

def sum_constants(F,x):
    children=F.children()

    if(len(children)==0):
        if not(eq(x,F)):
            return F
        return 0

    if(len(children)==1 or len(children)>2):
        return 0
    
    if(str(F.decl())=="+"):
        return sum_constants(children[0],x)+sum_constants(children[1],x)
    if(str(F.decl())=="*"):
        if(contains_x(F,x)):
            return 0
        return F
    return 0
            
            


def h(F,x):

    return sum_coefficients(F.children()[0],x)-sum_coefficients(F.children()[1],x)

def t(F,x):

    return sum_constants(F.children()[1],x)-sum_constants(F.children()[0],x)


    

def step3(F,x):

        children=F.children()
        #Si F est une variable ou une constante, pas de changement
        if(len(children)==0):
                return F
        if(len(children)==1):
                #Si F = Exists(x',F'(x',x)), on applique la methode de cooper sur F avec x comme constante.
                if(is_exists(F.sexpr())):
                        return methode_cooper(F)
                #Si F = Not(F'(x)), appel recurssif pour isoler les x dans F'(x)
                if(str(F.decl())=="Not"):
                        return Not(step3(children[0],x))
                return F.decl()(step3(children[0],x))


        #Si F est A<B on isole les x pour avoir hx<t      
        if(str(F.decl()) == "<"):
            return h(F,x)*x < t(F,x)
        #idem pour A>B
        if(str(F.decl()) == ">"):
            return h(F,x)*x > t(F,x)
        #Vu que les formules A==B ont ete elimines a l'etape 2, on sait qu'il s'agit d'une contrainte de divisibilite (a | b  <=> b%a==0)
        #On simplifie a | b par Exists(l,l*a==b)
        if(str(F.decl()) == "=="):
            l=Int("l")
            if(str(children[0].decl())=="%"):
                grand_children=children[0].children()
                a=grand_children[0]
                b=grand_children[1]
            else:
                grand_children=children[1].children()
                a=grand_children[0]
                b=grand_children[1]
            return methode_cooper(Exists(l,b*l==a))
            
        #Si F est de la forme P(F1(x),F2(x), ... Fn(x)) on renvoit P(step3(F1,x),...,step3(Fn,x))        
        result=step3(children[0],x)
        for i in range(1,len(children)):
            result=F.decl()(result,step3(children[i],x))
        return result

def step3(F,x):
    #Si F est une variable ou une constante, pas de changement
    if(type(F)==bool or type(F)==int or is_var(F) or is_const(F)):
        return F
    children=F.children()
    #Si F = Exists(x',F'(x',x)), on applique la methode de cooper sur F avec x comme constante.
    if(is_exists(F.sexpr())):
        return methode_cooper(F)
    if(is_not(F)):
        return Not(step3(children[0]))
    #Si F est A<B on isole les x pour avoir hx<t
    if(is_lt(F)):
        return h(F,x)*x < t(F,x)
    #Idem pour A>B
    if(is_gt(F)):
        return h(F,x)*x > t(F,x)
    #Vu que les formules A==B ont ete elimines a l'etape 2, on sait qu'il s'agit d'une contrainte de divisibilite (a | b  <=> b%a==0)
    #On simplifie a | b par Exists(l,l*a==b)
    if(is_eq(F)):
        if(is_mod(children[0])):
            grand_children=children[0].children()
            a,q=grand_children[0],grand_children[1]
            r=children[1]
            if contains_x(q,x) or not(type(q)==int):
                return False
            return ((sum_coefficients(a,x)-sum_coefficients(r,x))*x+(sum_constants(a,x)-sum_constants(r,x)))%q == 0
        
    #Si F est de la forme And/Or(F1,F2, ... Fn) on renvoit And/Or(step2(F1),...,step2(Fn))
    if(is_and(F) or is_or(F)):
        result=step3(children[0],x)
        for i in children[1:]:
            result=F.decl()(result,step3(i,x))
        return result

nbvar=0

def methode_cooper(P):
        print(P)
        if(is_exists(P.sexpr())):
            F=P.body()
            x=Var(0,IntSort())
            print(F)
            #Step 1
            result=step1(F)
            print(result)
            #Step 2
            result=step2(result)
            print(result)
            #Step 3
            result=step3(result,x)
            print(result)
            
            return True
        return False

x=Int("x")
y=Int("y")
F=And(3*x+7<=18,Not(x==1))


F=Exists(x,Exists(y,x==y))

print(methode_cooper(F))























