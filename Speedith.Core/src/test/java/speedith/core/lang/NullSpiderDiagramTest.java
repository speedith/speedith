/*
 *   Project: Speedith.Core
 * 
 * File name: NullSpiderDiagramTest.java
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

import org.junit.*;
import propity.util.Sets;

import java.io.IOException;
import java.util.HashSet;

import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class NullSpiderDiagramTest {

    private NullSpiderDiagram m_nsdInstance;
    private NullSpiderDiagram m_nsdInstance2;

    public NullSpiderDiagramTest() {
    }

    @BeforeClass
    public static void setUpClass() throws Exception {
    }

    @AfterClass
    public static void tearDownClass() throws Exception {
    }

    @Before
    public void setUp() {
        this.m_nsdInstance = NullSpiderDiagram.getInstance();
        this.m_nsdInstance2 = NullSpiderDiagram.getInstance();
    }

    @After
    public void tearDown() {
    }

    /**
     * Test of the {@link NullSpiderDiagram#getInstance()} method.
     */
    @Test
    public void testGetInstance() {
        NullSpiderDiagram expResult = NullSpiderDiagram.getInstance();
        NullSpiderDiagram result = NullSpiderDiagram.getInstance();
        assertEquals(expResult, result);
        assertSame(expResult, result);
        assertEquals(m_nsdInstance, result);
        assertSame(m_nsdInstance, result);
        assertEquals(expResult, m_nsdInstance2);
        assertSame(expResult, m_nsdInstance2);
    }

    /**
     * Test of equals method, of class NullSpiderDiagram.
     */
    @Test
    @SuppressWarnings("ObjectEqualsNull")
    public void testEquals() {
        NullSpiderDiagram instance = NullSpiderDiagram.getInstance();
        NullSpiderDiagram instance2 = NullSpiderDiagram.getInstance();
        boolean expResult = true;
        boolean result = instance.equals(instance2);
        assertEquals(expResult, result);
        result = instance2.equals(instance);
        assertEquals(expResult, result);
        expResult = false;
        result = instance.equals(null);
        assertEquals(expResult, result);
    }

    /**
     * Test of hashCode method, of class NullSpiderDiagram.
     */
    @Test
    public void testHashCode() {
        NullSpiderDiagram instance = NullSpiderDiagram.getInstance();
        int expResult = m_nsdInstance.hashCode();
        int result = instance.hashCode();
        assertEquals(expResult, result);
        assertEquals(expResult, m_nsdInstance2.hashCode());
        assertEquals(expResult, m_nsdInstance.hashCode());
    }

    /**
     * Test of toString method, of class NullSpiderDiagram.
     */
    @Test
    public void testToString_StringBuilder() throws IOException {
        StringBuilder sb = new StringBuilder();
        NullSpiderDiagram instance = NullSpiderDiagram.getInstance();
        instance.toString(sb);
        assertEquals(sb.toString(), NullSpiderDiagram.SDTextNullId);
        assertEquals(sb.toString(), instance.toString());
        assertEquals(sb.toString(), m_nsdInstance.toString());
        assertEquals(sb.toString(), m_nsdInstance2.toString());
    }

    @Test
    public void hashMap() {
        HashSet<SpiderDiagram> sds1 = new HashSet<>();
        sds1.add(m_nsdInstance);
        sds1.add(m_nsdInstance2);
        sds1.add(NullSpiderDiagram.getInstance());
        HashSet<SpiderDiagram> sds2 = new HashSet<>();
        sds2.add(m_nsdInstance);
        assertTrue(Sets.equal(sds1, sds2));
        assertEquals(sds1.size(), 1);
        assertEquals(sds2.size(), 1);
    }

    @Test
    public void hashMap1() {
        HashSet<SpiderDiagram> sds1 = new HashSet<>();
        sds1.add(m_nsdInstance);
        sds1.add(m_nsdInstance2);
        sds1.add(NullSpiderDiagram.getInstance());
        HashSet<SpiderDiagram> sds2 = new HashSet<>();
        assertFalse(Sets.equal(sds1, sds2));
        assertEquals(sds2.size(), 0);
        assertEquals(sds1.size(), 1);
    }
}
