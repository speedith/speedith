# Speedith

--------------------------------------------------------------------------------

Speedith is a diagrammatic theorem prover for [spider diagrams](http://en.wikipedia.org/wiki/Spider_diagram).

[![Build Status](https://travis-ci.org/speedith/speedith.svg?branch=master)](https://travis-ci.org/speedith/speedith)




--------------------------------------------------------------------------------

# Licence

Speedith is licenced under the MIT licence. Please read [LICENCE.md](LICENCE.md) for more information.

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

The build will result in a distributable package:

    Speedith.Gui/target/speedith-gui-0.0.1-SNAPSHOT-bin.zip

Unpack the archive and navigate into the unpacked `speedith/bin` folder.

Once in `speedith/bin` folder, execute the script that best matches your platform.

For example, on Windows you might want to execute either

    speedith-win32.bat

or

    speedith-win64.bat
