# Speedith

--------------------------------------------------------------------------------

Speedith is a diagrammatic theorem prover for [spider diagrams](http://en.wikipedia.org/wiki/Spider_diagram).

[![Build Status](https://travis-ci.org/urbas/speedith.svg?branch=master)](https://travis-ci.org/urbas/speedith)




--------------------------------------------------------------------------------

# Developer's Guide to _Speedith_ #

--------------------------------------------------------------------------------

## General Requirements

These requirements have to be checked only once. After you make sure you have
these, you can build Speedith at any time.

*   Maven (see [installation instructions](https://maven.apache.org/))

*   Java 7: Currently, the project does not build against Java 8.

Optional:

* Tesseract (needed for character recognition in drawn input):

  * Linux & OS X: Please follow [this guide](https://code.google.com/p/tesseract-ocr/wiki/ReadMe).

  * Windows: no need to install. Tesseract comes pre-packaged.

--------------------------------------------------------------------------------

## Building Speedith

Use Maven to build Speedith (in the root directory of your cloned Speedith repository):

    mvn install

--------------------------------------------------------------------------------

## Running Speedith

After a successful build, you will find this zip archive:

    speedith/Speedith.Gui/target/speedith-gui-0.0.1-SNAPSHOT-bin.zip

Unpacking the archive will create the `speedith` folder.

Navigate into the `speedith/bin` folder and execute the script that best matches your platform. For example, on Windows you might want to execute either

    speedith-win32.bat

or

    speedith-win64.bat