/*
 * File name: FormulaTranslator.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package diabelli.logic;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class FormulaTranslator {

    public static enum TranslationType {
        
        ToEquivalent(0),
        ToEntailed(1),
        ToEntailing(2);
        
        private final int typeId;

        private TranslationType(int typeId) {
            this.typeId = typeId;
        }

        public int getTypeId() {
            return typeId;
        }
        
    }
    FormulaFormatDescriptor getFromFormat() {
        throw new UnsupportedOperationException();
    }
    FormulaFormatDescriptor getToFormat() {
        throw new UnsupportedOperationException();
    }
    TranslationType getTranslationType() {
        throw new UnsupportedOperationException();
    }
    String getName() {
        throw new UnsupportedOperationException();
    }
    String getDescription() {
        throw new UnsupportedOperationException();
    }
    String getPrettyName() {
        throw new UnsupportedOperationException();
    }
}
