/*
 *   Project: Speedith.Core
 * 
 * File name: Zone.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2010 Matej Urbas
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
package speedith.lang;

import java.util.Iterator;
import java.util.TreeSet;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
class Zone implements Comparable<Zone> {
    // <editor-fold defaultstate="collapsed" desc="Private Fields">

    private TreeSet<String> inContours;
    private TreeSet<String> outContours;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    public int compareTo(Zone o) {
        if (o == null) {
            throw new NullPointerException();
        }
        if (this == o) {
            return 0;
        } else {
            int retVal = 0;
            Iterator<String> i1 = inContours.iterator(),
                    i2 = o.inContours.iterator();
            return retVal;
        }
    }
    // </editor-fold>
}
