{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_free_functors (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,8,2] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/dstoyano/.cabal/bin"
libdir     = "/Users/dstoyano/.cabal/lib/x86_64-osx-ghc-8.2.2/free-functors-0.8.2-EwWjsUdIHoU661fI0f99W9"
dynlibdir  = "/Users/dstoyano/.cabal/lib/x86_64-osx-ghc-8.2.2"
datadir    = "/Users/dstoyano/.cabal/share/x86_64-osx-ghc-8.2.2/free-functors-0.8.2"
libexecdir = "/Users/dstoyano/.cabal/libexec"
sysconfdir = "/Users/dstoyano/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "free_functors_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "free_functors_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "free_functors_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "free_functors_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "free_functors_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "free_functors_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
