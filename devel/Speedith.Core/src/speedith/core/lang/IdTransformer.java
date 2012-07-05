/*
 *   Project: Speedith.Core
 * 
 * File name: IdTransformer.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
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
package speedith.core.lang;

import java.util.ArrayList;

/**
 * A simple convenience implementation of the {@link Transformer} interface. All
 * its methods return {@code null} (except for {@link IdTransformer#isDone()},
 * which returns the value of the field {@link IdTransformer#done}). This means
 * that by default this transformer visits all the sub-diagrams in a spider
 * diagram.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class IdTransformer implements Transformer {

    /**
     * This field is initially set to {@code false}, which means that by default
     * this transformer visits all the sub-diagrams in a spider diagram.
     * <p>Implementations should simply set this field to {@code true} once
     * they are finished with the transformation.</p>
     */
    protected boolean done = false;

    @Override
    public SpiderDiagram transform(PrimarySpiderDiagram psd, int diagramIndex, int childIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        return null;
    }

    @Override
    public SpiderDiagram transform(NullSpiderDiagram nsd, int diagramIndex, int childIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        return null;
    }

    @Override
    public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, int childIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        return null;
    }

    @Override
    public boolean isDone() {
        return done;
    }
}
