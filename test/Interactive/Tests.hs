{-# LANGUAGE LambdaCase #-}

module Interactive.Tests where

import Control.Concurrent
import Data.Foldable
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO

import Test.Tasty
import Test.Tasty.HUnit
import System.Directory
import System.FilePath
import System.Exit
import System.IO
import System.Process

import Agda.Utils.Monad
import Utils

testDir :: FilePath
testDir = "test" </> "Interactive"

tests :: TestTree
tests = testGroup "Interactive"
  [ testCase "Naked" $ do
      runAgda [testDir </> "Naked.agda"] "Naked"
  , testCase "Issue1430" $ do
      runAgda ["--no-libraries", testDir </> "Issue1430.agda"] "Issue1430"
  , testCase "Load" $ do
      runAgda ["--no-libraries"] "Load"
  , let testName = "LoadTwice" in testCase testName $ do
      runAgdaInterleaved ["--no-libraries"] testName
        [ Left $ copyFile (testFile testName "agda.1") (testFile testName "agda")
        , Right $ ":load " ++ testFile testName "agda"
        , Right ":typeOf t1"
        , Left $ threadDelay 500000  -- Give the interactive mode half a second for :load
        , Left $ copyFile (testFile testName "agda.2") (testFile testName "agda")
        , Right $ ":load " ++ testFile testName "agda"
        , Right ":typeOf t1"
        , Right ":typeOf t2"
        , Right ":quit"
        ]
        (removeFile (testFile testName "agda"))
  ]
  where
    agdaArgs = [ "-I", "-i.", "-i..", "-itest/Interactive", "--ignore-interfaces" ]

    -- Run a test, reading interactive commands from testDir/testName.in
    runAgda :: [String] -> FilePath -> IO ()
    runAgda extraArgs testName = do
      inp <- TIO.readFile (testDir </> testName <.> "in")
      (c, out, err) <- readAgdaProcessWithExitCode (agdaArgs ++ extraArgs) inp
      assertBool ("Agda returned error code: " ++ show c) (c == ExitSuccess)
      verifyOutput (testFile testName "stdout.expected") out
      verifyOutput (testFile testName "stderr.expected") err

    runAgdaInterleaved :: [String] -> FilePath -> [Either (IO ()) String] -> IO () -> IO ()
    runAgdaInterleaved extraArgs testName inp cleanUp = do
      cp <- agdaProcess (agdaArgs ++ extraArgs)
      let fout = testFile testName "out"
          ferr = testFile testName "err"
      hout <- openFile fout WriteMode
      herr <- openFile ferr WriteMode
      (Just hin, _, _, ph) <- createProcess cp
        { std_in = CreatePipe, std_out = UseHandle hout, std_err = UseHandle herr }
      for_ inp $ \case
        Left io -> io
        Right s -> hPutStrLn hin s >> hFlush hin
      c <- waitForProcess ph
      assertBool ("Agda returned error code: " ++ show c) (c == ExitSuccess)
      out <- TIO.readFile fout
      err <- TIO.readFile ferr
      verifyOutput (testFile testName "stdout.expected") out
      verifyOutput (testFile testName "stderr.expected") err
      removeFile fout
      removeFile ferr
      cleanUp

    testFile :: String -> FilePath -> FilePath
    testFile testName suffix = testDir </> testName <.> suffix

    -- Check that every line in the file is a substring of the actual output.
    verifyOutput :: FilePath -> Text -> IO ()
    verifyOutput expectedFile actualOutput =
      whenM (doesFileExist expectedFile) $ do
        expected <- TIO.readFile expectedFile
        for_ (Text.lines expected) $
          assertBool ("Invalid stdout: " ++ show actualOutput) . (`Text.isInfixOf` actualOutput)
