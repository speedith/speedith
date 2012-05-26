/*
 *   Project: Speedith.Core
 * 
 * File name: MovableArrayListTest.java
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
package speedith.core.util;

import java.util.Arrays;
import org.junit.*;
import static org.junit.Assert.*;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class MovableArrayListTest {

    private final Number[] empty = new Number[]{};
    private final Integer[] initSourceInt = new Integer[]{9, -31, 43};
    private final Integer[] initDestinationInt = new Integer[]{3, 1, 7, 9, -1};
    private final Number[] initSourceNum = new Number[]{24, -98, 7.3, -54.6f, (byte) 32};
    private final Number[] initDestinationNum = new Number[]{3.6, 3f};
    private final Double[] initSourceDbl = new Double[]{24.0, -98.1, 7.3, -54.6, 32.7};
    private final Double[] initDestinationDbl = new Double[]{3.6, -32.982};

    public MovableArrayListTest() {
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
     * Test of moveTo method, of class MovableArrayList.
     */
    @Test
    public void testMoveTo() {
        MovableArrayList<Integer> source = new MovableArrayList<>(Arrays.asList(initSourceInt));
        MovableArrayList<Number> destination = new MovableArrayList<>(Arrays.asList(initDestinationNum));

        assertArrayEquals(initSourceInt, source.toArray());
        assertArrayEquals(initDestinationNum, destination.toArray());

        source.moveTo(destination);

        assertArrayEquals(empty, source.toArray());
        assertArrayEquals(initSourceInt, destination.toArray());
    }

    /**
     * Test of moveTo method, of class MovableArrayList.
     */
    @Test
    public void testMoveTo1() {
        MovableArrayList<Number> destination = new MovableArrayList<>(Arrays.asList(initDestinationNum));
        MovableArrayList<Double> source = new MovableArrayList<>(Arrays.asList(initSourceDbl));

        assertArrayEquals(initSourceDbl, source.toArray());
        assertArrayEquals(initDestinationNum, destination.toArray());

        source.moveTo(destination);

        assertArrayEquals(empty, source.toArray());
        assertArrayEquals(initSourceDbl, destination.toArray());
    }

    /**
     * Test of swapWith method, of class MovableArrayList.
     */
    @Test
    public void testSwapWith() {
        MovableArrayList<Number> source = new MovableArrayList<>(Arrays.asList(initSourceNum));
        MovableArrayList<Number> destination = new MovableArrayList<>(Arrays.asList(initDestinationNum));

        assertArrayEquals(initSourceNum, source.toArray());
        assertArrayEquals(initDestinationNum, destination.toArray());

        source.swapWith(destination);

        assertArrayEquals(initDestinationNum, source.toArray());
        assertArrayEquals(initSourceNum, destination.toArray());
    }

    /**
     * Test of move method, of class MovableArrayList.
     */
    @Test
    public void testMove() {
        MovableArrayList<Integer> source = new MovableArrayList<>(Arrays.asList(initSourceInt));
        MovableArrayList<Number> destination = new MovableArrayList<>(Arrays.asList(initDestinationNum));

        assertArrayEquals(initSourceInt, source.toArray());
        assertArrayEquals(initDestinationNum, destination.toArray());

        MovableArrayList.move(source, destination);

        assertArrayEquals(empty, source.toArray());
        assertArrayEquals(initSourceInt, destination.toArray());
    }

    /**
     * Test of swap method, of class MovableArrayList.
     */
    @Test
    public void testSwap() {
        MovableArrayList<Number> source = new MovableArrayList<>(Arrays.asList(initSourceNum));
        MovableArrayList<Number> destination = new MovableArrayList<>(Arrays.asList(initDestinationNum));

        assertArrayEquals(initSourceNum, source.toArray());
        assertArrayEquals(initDestinationNum, destination.toArray());

        MovableArrayList.swap(source, destination);

        assertArrayEquals(initDestinationNum, source.toArray());
        assertArrayEquals(initSourceNum, destination.toArray());
    }

    /**
     * Test of size method, of class MovableArrayList.
     */
    @Test
    public void testSize() {
        MovableArrayList<Number> destination = new MovableArrayList<>(Arrays.asList(initDestinationNum));
        MovableArrayList<Integer> source = new MovableArrayList<>(Arrays.asList(initSourceInt));

        assertEquals(initSourceInt.length, source.size());
        assertEquals(initDestinationNum.length, destination.size());
    }

    /**
     * Test of isEmpty method, of class MovableArrayList.
     */
    @Test
    public void testIsEmpty() {
        assertEquals(true, new MovableArrayList<>(new MovableArrayList<>()).isEmpty());
        assertEquals(true, new MovableArrayList<>(new MovableArrayList<>(Arrays.asList(empty))).isEmpty());
        assertEquals(true, new MovableArrayList<>().isEmpty());
        assertEquals(true, new MovableArrayList<>(54).isEmpty());
        assertEquals(true, new MovableArrayList<>(Arrays.asList(empty)).isEmpty());
        
        
        MovableArrayList<Integer> source = new MovableArrayList<>(Arrays.asList(initSourceInt));
        MovableArrayList<Number> destination = new MovableArrayList<Number>(source, true);
        assertEquals(true, source.isEmpty());
        assertEquals(false, destination.isEmpty());
        assertArrayEquals(initSourceInt, destination.toArray());
    }

    /**
     * Test of isEmpty method, of class MovableArrayList.
     */
    @Test
    public void testIsEmpty2() {
        assertEquals(false, new MovableArrayList<>(Arrays.asList(initSourceDbl)).isEmpty());
        assertEquals(false, new MovableArrayList<>(Arrays.asList(initSourceNum)).isEmpty());
        assertEquals(false, new MovableArrayList<>(Arrays.asList(initSourceInt)).isEmpty());
        assertEquals(false, new MovableArrayList<>(Arrays.asList(initDestinationDbl)).isEmpty());
    }

    /**
     * Test of contains method, of class MovableArrayList.
     */
    @Test
    public void testContains() {
//        System.out.println("contains");
//        Object o = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.contains(o);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of iterator method, of class MovableArrayList.
     */
    @Test
    public void testIterator() {
//        System.out.println("iterator");
//        MovableArrayList instance = new MovableArrayList();
//        Iterator expResult = null;
//        Iterator result = instance.iterator();
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of toArray method, of class MovableArrayList.
     */
    @Test
    public void testToArray_0args() {
//        System.out.println("toArray");
//        MovableArrayList instance = new MovableArrayList();
//        Object[] expResult = null;
//        Object[] result = instance.toArray();
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of toArray method, of class MovableArrayList.
     */
    @Test
    public void testToArray_GenericType() {
//        System.out.println("toArray");
//        T[] a = null;
//        MovableArrayList instance = new MovableArrayList();
//        Object[] expResult = null;
//        Object[] result = instance.toArray(a);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of add method, of class MovableArrayList.
     */
    @Test
    public void testAdd_GenericType() {
//        System.out.println("add");
//        Object e = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.add(e);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of remove method, of class MovableArrayList.
     */
    @Test
    public void testRemove_Object() {
//        System.out.println("remove");
//        Object o = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.remove(o);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of containsAll method, of class MovableArrayList.
     */
    @Test
    public void testContainsAll() {
//        System.out.println("containsAll");
//        Collection<?> c = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.containsAll(c);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of addAll method, of class MovableArrayList.
     */
    @Test
    public void testAddAll_Collection() {
//        System.out.println("addAll");
//        Collection<? extends E> c = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.addAll(c);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of addAll method, of class MovableArrayList.
     */
    @Test
    public void testAddAll_int_Collection() {
//        System.out.println("addAll");
//        int index = 0;
//        Collection<? extends E> c = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.addAll(index, c);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of removeAll method, of class MovableArrayList.
     */
    @Test
    public void testRemoveAll() {
//        System.out.println("removeAll");
//        Collection<?> c = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.removeAll(c);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of retainAll method, of class MovableArrayList.
     */
    @Test
    public void testRetainAll() {
//        System.out.println("retainAll");
//        Collection<?> c = null;
//        MovableArrayList instance = new MovableArrayList();
//        boolean expResult = false;
//        boolean result = instance.retainAll(c);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of clear method, of class MovableArrayList.
     */
    @Test
    public void testClear() {
//        System.out.println("clear");
//        MovableArrayList instance = new MovableArrayList();
//        instance.clear();
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of get method, of class MovableArrayList.
     */
    @Test
    public void testGet() {
//        System.out.println("get");
//        int index = 0;
//        MovableArrayList instance = new MovableArrayList();
//        Object expResult = null;
//        Object result = instance.get(index);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of set method, of class MovableArrayList.
     */
    @Test
    public void testSet() {
//        System.out.println("set");
//        int index = 0;
//        Object element = null;
//        MovableArrayList instance = new MovableArrayList();
//        Object expResult = null;
//        Object result = instance.set(index, element);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of add method, of class MovableArrayList.
     */
    @Test
    public void testAdd_int_GenericType() {
//        System.out.println("add");
//        int index = 0;
//        Object element = null;
//        MovableArrayList instance = new MovableArrayList();
//        instance.add(index, element);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of remove method, of class MovableArrayList.
     */
    @Test
    public void testRemove_int() {
//        System.out.println("remove");
//        int index = 0;
//        MovableArrayList instance = new MovableArrayList();
//        Object expResult = null;
//        Object result = instance.remove(index);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of indexOf method, of class MovableArrayList.
     */
    @Test
    public void testIndexOf() {
//        System.out.println("indexOf");
//        Object o = null;
//        MovableArrayList instance = new MovableArrayList();
//        int expResult = 0;
//        int result = instance.indexOf(o);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of lastIndexOf method, of class MovableArrayList.
     */
    @Test
    public void testLastIndexOf() {
//        System.out.println("lastIndexOf");
//        Object o = null;
//        MovableArrayList instance = new MovableArrayList();
//        int expResult = 0;
//        int result = instance.lastIndexOf(o);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of listIterator method, of class MovableArrayList.
     */
    @Test
    public void testListIterator_0args() {
//        System.out.println("listIterator");
//        MovableArrayList instance = new MovableArrayList();
//        ListIterator expResult = null;
//        ListIterator result = instance.listIterator();
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of listIterator method, of class MovableArrayList.
     */
    @Test
    public void testListIterator_int() {
//        System.out.println("listIterator");
//        int index = 0;
//        MovableArrayList instance = new MovableArrayList();
//        ListIterator expResult = null;
//        ListIterator result = instance.listIterator(index);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }

    /**
     * Test of subList method, of class MovableArrayList.
     */
    @Test
    public void testSubList() {
//        System.out.println("subList");
//        int fromIndex = 0;
//        int toIndex = 0;
//        MovableArrayList instance = new MovableArrayList();
//        List expResult = null;
//        List result = instance.subList(fromIndex, toIndex);
//        assertEquals(expResult, result);
//        // TODO review the generated test code and remove the default call to fail.
//        fail("The test case is a prototype.");
    }
}
