package spiderdrawer;

import static org.junit.Assert.*;

import org.junit.Test;

import spiderdrawer.shape.Circle;
import spiderdrawer.shape.Label;
import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;

public class ContainerTest {

	@Test
	public void singleToSingleContainer() {	
		Circle circle = new Circle(1,1,1);
		Label label = new Label('A',2,2);
		SingleContainer<Circle, Label> sc1 = new SingleContainer<Circle, Label>(label);
		SingleContainer<Label, Circle> sc2 = new SingleContainer<Label, Circle>(circle);
		sc1.set(circle, sc2);
		assertTrue(circle.equals(sc1.get()));
		assertTrue(label.equals(sc2.get()));
		
		sc1.set(null, sc2);
		assertTrue(sc1.get() == null);
		assertTrue(sc2.get() == null);
	}
	
	@Test
	public void multiToMultiContainer() {
		Circle circle = new Circle(1,1,1);
		Label label = new Label('A',2,2);
		MultiContainer<Circle, Label> mc1 = new MultiContainer<Circle, Label>(label);
		MultiContainer<Label, Circle> mc2 = new MultiContainer<Label, Circle>(circle);
		mc1.add(circle, mc2);
		assertTrue(mc1.contains(circle));
		assertTrue(mc2.contains(label));
		
		mc2.remove(label);
		assertTrue(!mc1.contains(circle));
		assertTrue(!mc2.contains(label));
		
		mc1.add(circle, mc2);
		Circle circle2 = new Circle(1,1,1);
		MultiContainer<Label, Circle> mc3 = new MultiContainer<Label, Circle>(circle2);
		mc1.add(circle2, mc3);
		assertTrue(mc2.contains(label));
		assertTrue(mc3.contains(label));
		
		mc1.removeAll();
		assertTrue(!mc1.contains(circle));
		assertTrue(!mc1.contains(circle2));
		assertTrue(!mc2.contains(label));
		assertTrue(!mc3.contains(label));
		
	}
	
	@Test
	public void singleToMultiContainer() {
		Circle circle = new Circle(1,1,1);
		Label label = new Label('A',2,2);
		MultiContainer<Circle, Label> mc1 = new MultiContainer<Circle, Label>(label);
		SingleContainer<Label, Circle> mc2 = new SingleContainer<Label, Circle>(circle);
		mc1.add(circle, mc2);
		assertTrue(mc1.contains(circle));
		assertTrue(mc2.get().equals(label));
		
		mc2.set(null, mc1);
		assertTrue(!mc1.contains(circle));
		assertTrue(mc2.get() == null);
		
		mc1.add(circle, mc2);
		Circle circle2 = new Circle(1,1,1);
		SingleContainer<Label, Circle> mc3 = new SingleContainer<Label, Circle>(circle2);
		mc1.add(circle2, mc3);
		assertTrue(mc2.get().equals(label));
		assertTrue(mc3.get().equals(label));
		
		mc1.removeAll();
		assertTrue(!mc1.contains(circle));
		assertTrue(!mc1.contains(circle2));
		assertTrue(mc2.get() == null);
		assertTrue(mc3.get() == null);
		
	}
}
