/*
 *   Project: Speedith.Core
 * 
 * File name: SimpleInferenceRuleTest.java
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
package speedith.core.reasoning.rules;

import org.junit.Test;
import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.DiagramVisitor;
import speedith.core.lang.SpiderDiagram;
import speedith.core.lang.reader.ReadingException;
import speedith.core.lang.reader.SpiderDiagramsReader;
import speedith.core.lang.reader.SpiderDiagramsReaderTest;

import java.util.ArrayList;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SimpleInferenceRuleTest {

    @Test
    public void testPositions() throws ReadingException {
        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_1).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_2).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1 || subDiagramIndex == 3) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_3).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1 || subDiagramIndex == 2 || subDiagramIndex == 3) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_4).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);
        
        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_5).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);
        
        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_6).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_7).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 1 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_8).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_9).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_10).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_11).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_12).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.EquivalencePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_13).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 1 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_14).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 1 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);

        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_15).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0 || subDiagramIndex == 2) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else if (subDiagramIndex == 1) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.NegativePosition);
                } else {
                    fail();
                }
            }
        }, true);
        
        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_16).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);
        
        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_17).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);
        
        SpiderDiagramsReader.readSpiderDiagram(SpiderDiagramsReaderTest.SD_EXAMPLE_18).visit(new DiagramVisitorImpl() {
            @Override
            public void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices) {
                if (subDiagramIndex == 0) {
                    assertEquals(SimpleInferenceRule.getPositionType(parents, childIndices), SimpleInferenceRule.PositivePosition);
                } else {
                    fail();
                }
            }
        }, true);
    }

    private static abstract class DiagramVisitorImpl implements DiagramVisitor<Void> {

        public DiagramVisitorImpl() {
        }

        @Override
        public void init(SpiderDiagram root) {
        }

        @Override
        public void end() {
        }

        @Override
        public boolean isDone() {
            return false;
        }

        @Override
        public Void getResult() {
            return null;
        }
    }
}
