/*
 *   Project: Speedith
 * 
 * File name: DiagramSelectorTest.java
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
package speedith.ui.selection.helpers;

import org.junit.*;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.RuleArg;
import speedith.core.reasoning.args.SpiderRegionArg;
import speedith.core.reasoning.args.selection.SelectionSequence;

import java.awt.*;
import java.util.Collection;

import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class DiagramSelectorTest {
    
    public DiagramSelectorTest() {
    }

    @BeforeClass
    public static void setUpClass() throws Exception {
    }

    @AfterClass
    public static void tearDownClass() throws Exception {
    }
    
    @Before
    public void setUp() {
    }
    
    @After
    public void tearDown() {
    }

    /**
     * Test of convertToRuleArg method, of class DiagramSelector.
     */
    @Test
    public void testConvertToRuleArg() {
    }

    /**
     * Test of showSelectionDialog method, of class DiagramSelector.
     */
    @Test
    public void testShowSelectionDialog() {
    }

    /**
     * Test of getSelector method, of class DiagramSelector.
     */
    @Test
    public void testGetSelector_Class_ObjectArr() {
        Class<SpiderRegionArg> ruleArgType = SpiderRegionArg.class;
        checkSelectors(ruleArgType);
    }

    private void checkSelectors(Class<? extends RuleArg> ruleArgType) {
        Collection<Class<? extends DiagramSelector>> selectors = DiagramSelector.getSelectors(ruleArgType);
        assertNotNull(selectors);
        assertTrue(selectors.size() > 0);
        if (selectors.size() == 1)
            assertNotNull(DiagramSelector.getSelector(ruleArgType));
        
        // All selectors must support the default constructor.
        for (Class<? extends DiagramSelector> selector : selectors) {
            assertNotNull(DiagramSelector.getSelector(DiagramSelector.getSelectorName(selector)));
            assertTrue(selector.isInstance(DiagramSelector.getSelector(DiagramSelector.getSelectorName(selector))));
        }
    }

    /**
     * Test of getSelector method, of class DiagramSelector.
     */
    @Test
    public void testGetSelector_String_ObjectArr() {
        // All selectors must support the default constructor.
        for (Class<? extends DiagramSelector> selector : DiagramSelector.getRegisteredSelectors()) {
            assertNotNull(DiagramSelector.getSelector(DiagramSelector.getSelectorName(selector)));
            assertTrue(selector.isInstance(DiagramSelector.getSelector(DiagramSelector.getSelectorName(selector))));
        }
    }

    /**
     * Test of getSupportedRuleArgs method, of class DiagramSelector.
     */
    @Test
    public void testGetSupportedRuleArgs() {
        for (Class<? extends RuleArg> class1 : DiagramSelector.getSupportedRuleArgs()) {
            checkSelectors(class1);
        }
    }

    /**
     * Test of registerProvider method, of class DiagramSelector.
     */
    @Test
    public void testRegisterProvider() {
        try {
            DiagramSelector.registerProvider(FakeDiagramSelector.class);
        } catch (Exception e) {
            assertNull(e);
        }
        Collection<Class<? extends DiagramSelector>> selectors = DiagramSelector.getSelectors(SpiderRegionArg.class);
        assertTrue(selectors.contains(FakeDiagramSelector.class));
        assertTrue(selectors.contains(SpiderRegionSelector.class));
       
        try {
            DiagramSelector.registerProvider(FakeDiagramSelector2.class);
            assertFalse("Should throw an exception here.", true);
        } catch (Exception e) {
        }
    }

    /**
     * Test of getSpiderRegionSelector method, of class DiagramSelector.
     */
    @Test
    public void testGetSpiderRegionSelector() {
    }
    
    @SelectorDetails(name="Spider region selector 2", targetRuleArg=SpiderRegionArg.class)
    private static class FakeDiagramSelector extends DiagramSelector<SpiderRegionArg> {

        @Override
        public SpiderRegionArg convertToRuleArg(SelectionSequence selection) {
            throw new UnsupportedOperationException("Not supported yet.");
        }

        @Override
        public SpiderRegionArg showSelectionDialog(Frame parent, SpiderDiagram diagram) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
        
    }
    
    @SelectorDetails(name="Spider region selector", targetRuleArg=SpiderRegionArg.class)
    private static class FakeDiagramSelector2 extends DiagramSelector<SpiderRegionArg> {

        @Override
        public SpiderRegionArg convertToRuleArg(SelectionSequence selection) {
            throw new UnsupportedOperationException("Not supported yet.");
        }

        @Override
        public SpiderRegionArg showSelectionDialog(Frame parent, SpiderDiagram diagram) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
        
    }
}
