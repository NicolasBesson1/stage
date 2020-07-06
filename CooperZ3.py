from z3 import *
x=Int('x')

'''METHODE DE COOPER'''
def step1(F):
        return Tactic("nnf")(F).as_expr()

def step2(F):
        children=F.children()
        if(len(children)==0):
                return F
        if(len(children)==1):
                if(str(F.decl())=="Not"):
                        grand_children=children[0].children()
                        if(len(grand_children)==2):
                                if(str(children[0].decl())=="=="):
                                        A=grand_children[0]
                                        B=grand_children[1]
                                        return Or(B>A,B<A)
                                if(str(children[0].decl())=="<"):
                                        A=grand_children[0]
                                        B=grand_children[1]
                                        return B<A+1
                                if(str(children[0].decl())==">"):
                                        A=grand_children[0]
                                        B=grand_children[1]
                                        return A<B+1

                return F
        A=children[0]
        B=children[1]         
        if(str(F.decl())=="<="):
                return A < B+1
        if(str(F.decl())==">="):
                return B < A+1
        if(str(F.decl())=="Distinct"):
                return Or(A<B,B<A)
        if(str(F.decl())=="=="):
                return And(A<B+1,B<A+1)
        for i in range(1,len(children)):
                result=F.decl()(result,step2(children[i]))

        return result
         
def step3(F,x):
        children=F.children()
        if(len(children)==0):
                return F
        if(len(children)==1):
                if(str(F.decl())=="Not"):
                        return step3(children[0],x)
                else:
                        return methode_cooper(children[0],x)
        #A finir
        

def methode_cooper(F,x):
        #Step 1
        result=step1(F)
        #Step 2
        result=step2(result)

        return result

F=And(3*x+7<=18,Not(x==1))
print(F.decl()(F.children()[0],F.children()[1]))


print(methode_cooper(F,x))
