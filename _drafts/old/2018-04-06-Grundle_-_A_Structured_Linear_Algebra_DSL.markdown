---
author: philzook58
comments: true
date: 2018-04-06 18:39:14+00:00
layout: post
link: https://www.philipzucker.com/?p=1033
published: false
slug: Grundle - A Structured Linear Algebra DSL
title: Grundle - A Structured Linear Algebra DSL
wordpress_id: 1033
---

Checkout Spiral

    
    
    -- Morhpism ~ Pure
    -- Comp ~ Free?... 
    data CatExpr a = Morphism a   -- a literal 
    				| Comp (CatExpr a) (CatExpr a) 
    				| Dup  -- \a -> (a,a)
    				| Exl -- (\a, b -> a)
    				| Exr 
    				| Id -- \a -> a
    				| Tensor (CatExpr) (CatExpr) -- (a->b) (c -> d) -> (a,c) -> (b,d)
    
    -- data CatExprF f a = Morphism a | Comp (f a) (f a) | Dup | Exl | Exr | 
    
    runcat (Morphism f) = f
    runcat (Comp f g) = (runcat f) . (runcat g)
    runcat Dup = \a -> (a,a)
    runcat Exl = \(a,b) -> a
    runcat Exr = \(a,b) -> b
    runcat Id = id
    runcat (Tensor f g) = (runcat f) *** (runcat g) 
    
    
    runcatL (Morphism f) = f
    runcatL (Comp f g) = dot (runcatL f) (runcatL g) -- matrix multiplication
    runcatL Dup = \a -> (a,a) -- all of these are no good for linear
    runcatL Exl = \(a,b) -> a
    runcatL Exr = \(a,b) -> b
    runcatL Id = eye
    runcatL (Tensor f g) = kron (runcatL f) (runcatL g) 
    
    
    
    -- Ignore actual implementation.
    -- or just do it fast. Implement everything as dense.
    
    data Structure = Tri | Banded  | Diag | Dense | Scalar   --  | ExprMat | Function
    
    -- GType may want to be a type level tag. We really shouldn't be considering heterogenous typing of sclars
    
    data GType = Doub | ComplexDoub | FixedPrec
    
    data GDef = Function | Fixed | Pointer | Lit -- Var | Const | AutoDiff 
    
    data VarConst = Var | Const 
    
    type Shape = (Int,Int)
    
    -- or ID?
    type Name = String
    -- Consider two things: Vectors and Matrices. They are internally tensors basically
    
    -- Consider paring down on the possiblieis
    -- I think I have too many.
    data GMatExpr = Base Structure GType Name VarConst Shape
    				  | MatMul GrundleExpr GrundleExpr
    				  | Plus GrundleExpr GrundleExpr
    				  | Kron GrundleExpr GrundleExpr
    				  | Block GrundleExpr GrundleExpr GrundleExpr GrundleExpr
    				  | BlockTriDiag
    				  | BlockDiag -- Also equal to 
    				  |
    				  | HStack GrundleExpr GrundleExpr
    				  | VStack GrundleExpr GrundleExpr
    				  | Row GVecExpr
    				  | Col GVecExpr
    				  | Outer GVecExpr GVecExpr 
    
    
    -- Seperate out square and non square Matrices?
    
    data GVecExpr = BaseVec
    				| Kron
    				| Stack
    				| 
    
    
    data GScalarExpr = Trace GMatExpr 
    				|  Dot VecExpr VecExpr
    				|
    
    data GFunction = GFunction GMatExpr GVecExpr -- A x + b
    data GConstraint = GConstraint GFunction GFunction -- Ax + b == Bx + d
    data GQuadExpr = GQuadExpr GMatExpr GVecExpr Scalar -- xAx + bx + c
    
    
    
    checkShapes :: GrundleExpr -> Maybe String -- report error location
    
    type GrundleEnv a = Map Name a
    
    runGrundHMatrix :: GrundExp -> GrundleEnv HMatrix -> HMatrix 
    interpret :: GrundeExpr -> 
    
    
    -- Are things at this level worth anything? Maybe. 
    
    
    
    



