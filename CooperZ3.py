from z3 import *

'''METHODE DE COOPER'''
def step1(F):
        #Mettre F en nnf
        return Tactic("nnf")(F).as_expr()

def is_exists(S):
    return S.split(" ")[0]=="(exists"

def gerer_egalite(F):
        #Si F est a%q==r on renvoit a-r%q==0
        #Sinon on renvoit And(A<B+1, B<A+1)
        children=F.children()
        A=children[0]
        B=children[1]      
        if(str(A.decl())=="%"):
            grand_children=A.children()
            a=grand_children[0]
            q=grand_children[1]
            r=B
            return (a-r % q) == 0
        if(str(B.decl()) == "%"):
            grand_children=B.children()
            a=grand_children[0]
            q=grand_children[1]
            r=A
            return (a-r % q) == 0
        return And(A<B+1,B<A+1)
        
        
def step2(F):
        children=F.children()
        #Si F est une variable ou une constante, pas de changement
        if(len(children)==0):
                return F
        #Cas ou F est une fonction a un parametre
        if(len(children)==1):
                #Si F = Exists(x,F'(x)), on applique la methode de cooper sur F.
                if(is_exists(F.sexpr())):
                    return methode_cooper(F)
                #Si F est une formule de la forme Not(...)
                if(str(F.decl())=="Not"):
                        grand_children=children[0].children()
                        if(len(grand_children)==2):
                                
                                if(str(children[0].decl())=="=="):
                                        # Si F est de la forme Not(A%B==0) on laisse la formule telle qu'elle est
                                        if(len(grand_children[0].children())==2 and str(grand_children[0].decl())=="%"):
                                            return Not(children[0])
                                        if(len(grand_children[1].children())==2 and str(grand_children[1].decl())=="%"):
                                            return Not(children[0])
                                        A=grand_children[0]
                                        B=grand_children[1]
                                        #Si F est de la forme Not(A==B) on transforme pour avoir A<B ou B<A
                                        return Or(A<B,B<A)
                                if(str(children[0].decl())=="<"):
                                        #Si F est de la forme Not(A<B) on renvoit B < A+1
                                        A=grand_children[0]
                                        B=grand_children[1]
                                        return B<A+1
                                if(str(children[0].decl())==">"):
                                        #Si F est de la forme Not(B<A) on renvoit A < B+1
                                        A=grand_children[0]
                                        B=grand_children[1]
                                        return A<B+1
                return F.decl()(step2(children[0]))
        A=children[0]
        B=children[1]         
        if(str(F.decl())=="<="):
                #A<=B  est remplace par A<B+1
                return A < B+1
        if(str(F.decl())==">="):
                #B<=A est remplace par B<A+1
                return B < A+1
        if(str(F.decl())=="Distinct"):
                #Meme cas de Not(A==B)
                return Or(A<B,B<A)
        if(str(F.decl())=="=="):
                #Si F est a%q==r on renvoit a-r%q==0
                #Sinon on renvoit And(A<B+1, B<A+1)
                return gerer_egalite(F)

        result=step2(children[0])
        #Si F est de la forme P(F1,F2, ... Fn) on renvoit P(step2(F1),...,step2(Fn))
        for i in range(1,len(children)):
                result=F.decl()(result,step2(children[i]))

        return result


def sum_coefficients(F,x):
    print("tetita = " + str(Var(0,s=Int)))
    children=F.children()
    if(F==x):
        return 1
 
    if(len(children)==0 or len(children)==1 or len(children)>2):
        return 0
    
    if(str(F.decl())=="*"):
        if(children[0]==x):
            return children[1]
        elif(children[1]==x):
            return children[0]
        else:
            return 0  
    
    if(str(F.decl())=="+"):
        return sum_coefficients(children[0],x)+sum_coefficients(children[1],x)
    return 0


def contains_x(F,x):
    children=F.children()
    if(len(children)==0):
        return x==F

    result=False
    for i in children:
        result=result or contains_x(i,x)
    return result
    
    

def sum_constants(F,x):
    print("conchita = " + str(x))
    children=F.children()

    if(len(children)==0):
        if not(x==F):
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
    print("culo = " + str(x))
    return sum_coefficients(F.children()[0],x)-sum_coefficients(F.children()[1],x)

def t(F,x):
    print("pito = " + str(x))
    return sum_constants(F.children()[1],x)-sum_constants(F.children()[0],x)


    

def step3(F,x):
        print("ano = " + str(x))
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

def methode_cooper(P):
        if(is_exists(P.sexpr())):
            F=P.children()[0]
            x=Int(P.var_name(0))
            
            #Step 1
            result=step1(F)
            #Step 2
            result=step2(result)
            print(result)
            #Step 3
            result=step3(result,x)
            print(result)
            return True



x=Int("x")
F=And(3*x+7<=18,Not(x==1))


print(methode_cooper(Exists(x,F)))



