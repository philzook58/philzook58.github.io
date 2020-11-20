---
author: philzook58
comments: true
date: 2017-12-12 14:03:41+00:00
layout: post
link: https://www.philipzucker.com/using-purescript-servant-bridge/
slug: using-purescript-servant-bridge
title: Using the Purescript Servant Bridge
wordpress_id: 941
tags:
- haskell
- purescript
- servant
---

Alright, here is some garbage code. Hope it helps you, sorry if it confuses you.

Checkout the Counter example

https://github.com/eskimor/servant-purescript/tree/master/examples/central-counter

that is where I pulled everything from. I ripped out just about everything fancy just so you and I can see the truly bare bones example.

It's mostly boiler plate on the generator side.

He does a couple fancier things that you may want, like rearranging names and changing folders. Here is a more basic example

This goes in app/PSGenerator.ps if you're using a stack template

    
    {-# LANGUAGE AutoDeriveTypeable    #-}
    {-# LANGUAGE DataKinds             #-}
    {-# LANGUAGE FlexibleInstances     #-}
    {-# LANGUAGE MultiParamTypeClasses #-}
    {-# LANGUAGE OverloadedStrings     #-}
    {-# LANGUAGE ScopedTypeVariables   #-}
    {-# LANGUAGE TypeOperators         #-}
    
    module Main where
    
    import           Control.Applicative
    import           Control.Lens
    import           Data.Aeson
    import           Data.Monoid
    import           Data.Proxy
    import qualified Data.Set                           as Set
    --import           Data.Text                          (Text)
    import qualified Data.Text                          as T
    import qualified Data.Text.Encoding                 as T
    import qualified Data.Text.IO                       as T
    import           Language.PureScript.Bridge
    import           Language.PureScript.Bridge.PSTypes
    import           Servant.API
    import           Servant.PureScript
    import           Servant.Subscriber.Subscribable
    
    import qualified Lib
    
    
    myBridge :: BridgePart
    myBridge = defaultBridge
    
    data MyBridge
    
    myBridgeProxy :: Proxy MyBridge
    myBridgeProxy = Proxy
    
    instance HasBridge MyBridge where
      languageBridge _ = buildBridge myBridge
    
    -- List all the types you want to end up in ServerTypes.purs Auto builds lenses too?
    myTypes :: [SumType 'Haskell]
    myTypes =  [
               mkSumType (Proxy :: Proxy Lib.User)
    --          , mkSumType (Proxy :: Proxy Lib.Hello)
              ]
    
    mySettings :: Settings
    mySettings = defaultSettings
    
    main :: IO ()
    main = do
      let frontEndRoot = "frontend/src"
      writeAPIModuleWithSettings mySettings frontEndRoot myBridgeProxy Lib.userAPI'
      writePSTypes frontEndRoot (buildBridge myBridge) myTypes


Mostly things can just be the defaults. Look at the Counter Example for some more config stuff you can do.

You do need to separate out the user json api by itself. If you hand writeAPIModuleWithSettings an api that has the RAW serving the index.html, it freaked out. Maybe there is a way to handle that, but it's not like that is probably what you want anyhow.

The myTypes Sum Type you want to add to for every type that you want to export over to purescript. frontEndRoot is where the generated files will go.

The Proxy business is a bunch of typelevel programming boilerplate. So is the empty MyBridge type.

There is basically no content to this code.

You also need to add this app/PSGenerator.hs file to your cabal file.

    
    executable psGenerator
      hs-source-dirs:      app
      main-is:             PSGenerator.hs
      other-modules:       Lib
      -- Other library packages from which modules are imported.
      build-depends:       base >=4.8 && < 6.0
                         , aeson
                         , containers
                         , filepath
                         , ghc-mod
                         , http-api-data
                         , http-types
                         , lens
                         , mainland-pretty
                         , purescript-bridge
                         , servant
                         , servant-foreign
                         , servant-purescript
                         , servant-subscriber
                         , text
                         , servant-server
                         , wai
                         , warp
                         , bytestring
    
      -- Directories containing source files.
      hs-source-dirs:      src
    
      -- Base language which the package is written in.
      default-language:    Haskell2010




Every time you want to run the generator, you need to run

stack exec psGenerator



This then will put an API file and a Data type file into your purescript source in frontend/src

Using the API is a touch annoying but correct. If you look at the generated signature

    
    getUsers :: forall eff m.
                MonadAsk (SPSettings_ SPParams_) m => MonadError AjaxError m => MonadAff ( ajax :: AJAX | eff) m
                => m (Array User)


There are a lot of constraints you need to satisfy in the monad m in order to call this thing. You need a monad that is Reader-like for getting the SPSettings_, needs to handle a Possible AjaxError, and needs to be an Aff-like monad. Woof.

It makes sense that you'd want to do all of this, but it is a burdensome mental overhead to get started.

Here's some very basic source that shows how to at least get to the stage where you can log it the resulting request. I'm just dumping the error like a bad boy.

    
    module Main where
    import Prelude
    
    
    import Control.Monad.Aff (Aff)
    import Control.Monad.Aff.Console
    import Control.Monad.Trans.Class
    import Data.Maybe
    import Control.Monad.Eff.Console (CONSOLE)
    
    import ServerAPI
    import Lib (User(..), _User)
    
    import Control.Monad.Aff
    import Control.Monad.Eff.Class
    import Data.Either
    import Control.Monad.Reader.Trans
    import Control.Monad.Except.Trans
    import Control.Monad.Eff.Exception (EXCEPTION)
    import Network.HTTP.Affjax (AJAX, get)
    
    import Servant.PureScript.Affjax
    import Servant.PureScript.Settings
    
    import Data.Array ((!!))
    import Unsafe.Coerce 
    
    import Data.Lens
    import Data.Symbol (SProxy(..))
    import Data.Lens.Record (prop)
    import Data.Traversable
    
    
    settings = defaultSettings $ SPParams_ { baseURL : "http://localhost:9000/" }
    
    
    
    type MySettings = SPSettings_ SPParams_
    type APIEffect eff = ReaderT MySettings (ExceptT AjaxError (Aff ( ajax :: AJAX, err :: EXCEPTION  | eff)))
    
    
    
    runEffect :: forall eff. MySettings -> APIEffect eff (Array User) -> Aff ( ajax :: AJAX, err :: EXCEPTION | eff) (Array User)
    runEffect settings m = do
        er <- runExceptT $ runReaderT m settings
        case er of
          Left err -> pure $ []
          Right v -> pure v
    
    
    getName :: User -> String
    getName (User {name : n }) = n
    
    name :: forall a b r. Lens { name :: a | r } { name :: b | r } a b
    name = prop (SProxy :: SProxy "name")
    
    main = launchAff do
              users <- runEffect settings getUsers
              log $ maybe "No name" (view $ _User <<< name) (users !! 1 )
              log $ (view $ traversed <<< _User <<< name) users
    
    


Note that you have to install purescript-servant-support as it tells you when you run psGenerator. I've been using psc-package. It is often helpful to go in to the psc-package.json file and update to the latest package-set. Just a little tip.

You see that the ExceptT handles the AjaxError and the ReaderT supplies the settings, which uses the defaults + a baseURL to point the request to

The whole thing is run inside an Aff monad.



Here's the basic servant code

    
    {-# LANGUAGE DataKinds #-}
    {-# LANGUAGE DeriveGeneric #-}
    {-# LANGUAGE FlexibleInstances #-}
    {-# LANGUAGE GeneralizedNewtypeDeriving #-}
    {-# LANGUAGE MultiParamTypeClasses #-}
    {-# LANGUAGE OverloadedStrings #-}
    {-# LANGUAGE RankNTypes #-}
    {-# LANGUAGE ScopedTypeVariables #-}
    {-# LANGUAGE TypeOperators #-}
    module Lib
        ( startApp
        , app
        , userAPI
        , userAPI'
        , Hello
        , User
        ) where
    
    --import Prelude ()
    --import Prelude.Compat
    
    --import Control.Monad.Except
    --import Control.Monad.Reader
    --import Data.Aeson.Compat
    import Data.Aeson.Types
    --import Data.Attoparsec.ByteString
    import Data.ByteString (ByteString)
    import Data.List
    import Data.Maybe
    --import Data.String.Conversions
    --import Data.Time.Calendar
    import GHC.Generics
    --import Lucid
    --import Network.HTTP.Media ((//), (/:))
    import Network.Wai
    import Network.Wai.Handler.Warp
    import Servant
    --import System.Directory
    --import Text.Blaze
    --import Text.Blaze.Html.Renderer.Utf8
    import qualified Data.Aeson.Parser
    --import qualified Text.Blaze.Html
    import Data.Text  (Text)
    
    
    
    data User = User
      { name :: String
      , age :: Int
      , email :: String
      } deriving (Eq, Show, Generic)
    
    instance FromJSON User
    instance ToJSON User
    
    instance FromJSON Hello
    instance ToJSON Hello
    
    users1 :: [User]
    users1 =
      [ User "Isaac Newton"    372 "isaac@newton.co.uk" 
      , User "Albert Einstein" 136 "ae@mc2.org"         
      ]
    
    type UserAPI = "users" :> Get '[JSON] [User] 
    type UserAPI1 = UserAPI :<|> Raw
    
    server1 :: Server UserAPI1
    server1 = return users1 :<|> serveDirectoryFileServer "./frontend"
    
    userAPI :: Proxy UserAPI1
    userAPI = Proxy
    
    userAPI' :: Proxy UserAPI
    userAPI' = Proxy
    
    -- 'serve' comes from servant and hands you a WAI Application,
    -- which you can think of as an "abstract" web application,
    -- not yet a webserver.
    app1 :: Application
    app1 = serve userAPI server1
    
    
    
    main :: IO ()
    main = do putStrLn "on port 9000"
              run 9000 app1
    
    startApp = main
    app = app1




Again, I started using the stack servant template, whose directory structure I'm complying with.



Edit: Some more comments: Purescript bridge is a seperate project from servant-purescript. Purescript bridge will translate your Haskell types. Servant purescript writes your api calls. The two lines in the main of PSGenerator.hs do these sepearte tasks. the writeAPI writes the API calls and  writePSTypes writes the types.

If you want to transport a parametrized data type like (Maybe a) in the myTypes things, hand the type a special type from here

https://hackage.haskell.org/package/purescript-bridge-0.11.1.2/docs/Language-PureScript-Bridge-TypeParameters.html

works like a charm




