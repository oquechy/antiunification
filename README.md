# Anti-unification
Translating intersection types to polymorphic with an anti-unification. Algorithm based on Embedding Second-Order Type System into an Intersection Type System (1995), a work by Yokouchi H.

# Example
Translation of a typing of self-application term (\x.xx) from the intersection type system to the polymorphic type system. First we define two type variables and a function type from the one of them to the other in the intersection type system:

    ghci> let argument = IVar "t"
    ghci> let result = IVar "s"
    ghci> let function = IFun argument result 
    
Now we build an intersection type of the function and it's argument. 
    
    ghci> let intersection = Both argument function
    
The type of the self-application then derived as a function type from the intersection to the result.  
    
    ghci> let selfApplication = IFun intersection result
    
Now lets translate this intersection type to the polymorfic system:

    ghci> tr selfApplication
    (∀a1.a1) -> (s)
      
