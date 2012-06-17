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

import propity.util.MovableArrayList;
import java.util.*;
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
    private final ArrayList<Object[]> allArrays = new ArrayList<>(Arrays.asList(new Object[][]{
                empty,
                initDestinationDbl,
                initDestinationInt,
                initDestinationNum,
                initSourceDbl,
                initSourceInt,
                initSourceNum
            }));

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
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            for (int i = 0; i < arr.length; i++) {
                Object o = arr[i];
                assertTrue(a.contains(o));
            }
        }
    }

    /**
     * Test of iterator method, of class MovableArrayList.
     */
    @Test
    public void testIterator() {
        // Forward iterator:
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            int c = 0;
            for (Object o : a) {
                assertEquals(arr[c++], o);
            }
            assertEquals(arr.length, c);
        }
    }

    /**
     * Test of listIterator method, of class MovableArrayList.
     */
    @Test
    public void testListIterator_0args() {
        Random rnd = new Random(0xff8c983846dfe0f9L);
        double probJumpBack = 0.2;
        iteratorTraversalTest(rnd, probJumpBack);
        iteratorTraversalTest(new Random(), probJumpBack);
    }

    private void iteratorTraversalTest(Random rnd, double probJumpBack) {
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            ListIterator<Object> lIter = a.listIterator();
            int idx = 0;
            while (true) {
                if (rnd.nextDouble() < probJumpBack) {
                    if (lIter.hasPrevious()) {
                        Object cur = lIter.previous();
                        assertEquals(arr[--idx], cur);
                    } else {
                        break;
                    }
                } else {
                    if (lIter.hasNext()) {
                        Object cur = lIter.next();
                        assertEquals(arr[idx++], cur);
                    } else {
                        break;
                    }
                }
            }
            assertTrue(String.format("`idx` should be either %d or %d, was %d.", 0, arr.length - 1, idx), arr.length == idx || idx == 0);
        }
    }

    private void iteratorFromTraversalTest(Random rnd, double probJumpBack, int iterations) {
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            for (int i = 0; i < iterations; i++) {
                int fromIndex = arr.length > 0 ? rnd.nextInt(arr.length) : 0;
                ListIterator<Object> lIter = a.listIterator(fromIndex);
                int idx = fromIndex;
                while (true) {
                    if (rnd.nextDouble() < probJumpBack) {
                        if (lIter.hasPrevious()) {
                            Object cur = lIter.previous();
                            assertEquals(arr[--idx], cur);
                        } else {
                            break;
                        }
                    } else {
                        if (lIter.hasNext()) {
                            Object cur = lIter.next();
                            assertEquals(arr[idx++], cur);
                        } else {
                            break;
                        }
                    }
                }
                assertTrue(String.format("`idx` should be either %d or %d, was %d.", 0, arr.length - 1, idx), arr.length == idx || idx == 0);
            }
        }
    }

    /**
     * Test of listIterator method, of class MovableArrayList.
     */
    @Test
    public void testListIterator_int() {
        Random rnd = new Random(0xff8c983846dfe0f9L);
        double probJumpBack = 0.2;
        int iterations = 10;
        iteratorFromTraversalTest(rnd, probJumpBack, iterations);
        iteratorFromTraversalTest(new Random(), probJumpBack, iterations);
    }

    /**
     * Test of toArray method, of class MovableArrayList.
     */
    @Test
    public void testToArray_0args() {
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            assertArrayEquals(arr, a.toArray());
        }
    }

    /**
     * Test of toArray method, of class MovableArrayList.
     */
    @Test
    public void testToArray_GenericType() {
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            assertArrayEquals(arr, a.toArray(new Object[]{}));
        }
    }

    /**
     * Test of add method, of class MovableArrayList.
     */
    @Test
    public void testAdd_GenericType() {
        final Object added = "Test";
        for (Object[] arr : allArrays) {
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            a.add(added);
            assertEquals(arr.length + 1, a.size());
            assertEquals(added, a.get(arr.length));
            if (arr.length > 0) {
                assertEquals(arr[arr.length - 1], a.get(arr.length - 1));
            }
            a.remove(arr.length);
            assertArrayEquals(arr, a.toArray());
        }
    }

    /**
     * Test of remove method, of class MovableArrayList.
     */
    @Test
    public void testRemove_Object() {
        Object removed;
        Random rnd = new Random(0xff8c983846dfe0f9L);
        for (Object[] arr : allArrays) {
            if (arr.length < 1) {
                continue;
            }
            MovableArrayList<Object> a = new MovableArrayList<>(Arrays.asList(arr));
            int rmIdx = rnd.nextInt(arr.length);
            removed = a.remove(rmIdx);
            assertEquals(arr.length - 1, a.size());
            assertEquals(removed, arr[rmIdx]);
            a.add(rmIdx, removed);
            assertArrayEquals(arr, a.toArray());
        }
    }

    /**
     * Test of containsAll method, of class MovableArrayList.
     */
    @Test
    public void testContainsAll() {
        for (Object[] arr : allArrays) {
            final List<Object> asList = Arrays.asList(arr);
            MovableArrayList<Object> a = new MovableArrayList<>(asList);
            assertTrue(a.containsAll(a));
            assertTrue(a.containsAll(asList));
            assertTrue(asList.containsAll(a));
        }
    }

//    /**
//     * Test of addAll method, of class MovableArrayList.
//     */
//    @Test
//    public void testAddAll_Collection() {
//    }
//
//    /**
//     * Test of addAll method, of class MovableArrayList.
//     */
//    @Test
//    public void testAddAll_int_Collection() {
//    }
//
//    /**
//     * Test of removeAll method, of class MovableArrayList.
//     */
//    @Test
//    public void testRemoveAll() {
//    }
//
//    /**
//     * Test of retainAll method, of class MovableArrayList.
//     */
//    @Test
//    public void testRetainAll() {
//    }
//
//    /**
//     * Test of clear method, of class MovableArrayList.
//     */
//    @Test
//    public void testClear() {
//    }
//
//    /**
//     * Test of get method, of class MovableArrayList.
//     */
//    @Test
//    public void testGet() {
//    }
//
//    /**
//     * Test of set method, of class MovableArrayList.
//     */
//    @Test
//    public void testSet() {
//    }
//
//    /**
//     * Test of add method, of class MovableArrayList.
//     */
//    @Test
//    public void testAdd_int_GenericType() {
//    }
//
//    /**
//     * Test of remove method, of class MovableArrayList.
//     */
//    @Test
//    public void testRemove_int() {
//    }
//
//    /**
//     * Test of indexOf method, of class MovableArrayList.
//     */
//    @Test
//    public void testIndexOf() {
//    }
//
//    /**
//     * Test of lastIndexOf method, of class MovableArrayList.
//     */
//    @Test
//    public void testLastIndexOf() {
//    }
//
//    /**
//     * Test of subList method, of class MovableArrayList.
//     */
//    @Test
//    public void testSubList() {
//    }
}
