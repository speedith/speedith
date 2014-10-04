package spiderdrawer.shape;

import java.awt.AlphaComposite;
import java.awt.Color;
import java.awt.Graphics2D;
import java.awt.Rectangle;
import java.awt.geom.Area;
import java.awt.geom.Ellipse2D;
import java.util.ArrayList;

import spiderdrawer.exception.EmptyContainerException;
import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Shape;


public class Shading implements Deletable, Drawable {
	
	/*
	 *  included\excluded
	 */
	private ArrayList<Shape> shapeList;
	SingleContainer<Box, Shading> box;
	MultiContainer<Circle, Shading> included;
	Freeform freeform;
	
	public Shading() {
	}
	
	private void createContainers() {
		box = new SingleContainer<Box, Shading>(this);
		included = new MultiContainer<Circle, Shading>(this);
	}
	
	public static Shading create(Freeform freeform, ArrayList<Shape> shapeList) {
		Shading shading = new Shading();
		shading.createContainers();
		shading.freeform = freeform;
		shading.shapeList = shapeList;
		shading.compute();
		return shading.checkExists()? null : shading;
	}
	
	public boolean checkExists() {
		if (included.size() == 0) {
			return box.get() == null || box.get().shading.get() != this;
		}
		Shading[] shadings = Arrays.shadingArray(shapeList);
		for (int i = 0; i < shadings.length; i++) {
			if (shadings[i].included.size() == included.size() && included.containsAll(shadings[i].included))
				return true;
		}
		
		return false;
	}
	
	
	public void compute() {
		Circle[] circles = Arrays.circleArray(shapeList);
		computeIncluded(circles);
		if (included.isEmpty())
			computeBox();
	}
	
	public void computeBox() {
		/* Check if it overlaped with any circles */
		Circle[] circles = Arrays.circleArray(shapeList);
		for (int i = 0; i < circles.length; i++)
			if (circles[i].intersects(freeform))
				return;
		
		Box[] boxes = Arrays.boxArray(shapeList);
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].shading.get() == null && boxes[i].contains(freeform) && boxes[i].innerBoxes.size() == 0)
				box.set(boxes[i], boxes[i].shading);
		}
	}
	
	public String asString() throws EmptyContainerException {
		String result = "([";
		for (int i = 0; i < included.size(); i++) {
			result += "\"" + included.get(i).label.getWExc("Label").getChar() + "\"";
			if (i != included.size()-1)
				result += ", ";
		}
		result += "],[";
		ArrayList<Circle> excluded = getExcluded();
		if (excluded != null) {
			for (int i = 0; i < excluded.size(); i++) {
				result += "\"" + excluded.get(i).label.getWExc("Label").getChar() + "\"";
				if (i != excluded.size()-1)
					result += ", ";
			}
		}
		return result + "])";
	}
	
	protected ArrayList<Circle> getExcluded() {
		Box box;
		if (included.size() > 0 && included.get(0).boxes.size() == 1)
			box = included.get(0).boxes.get(0);
		else if (this.box.get() != null)
			box = this.box.get();
		else
			return null;
		@SuppressWarnings("unchecked")
		ArrayList<Circle> excluded = (ArrayList<Circle>) box.circles.list().clone();
		excluded.removeAll(included.list());
		return excluded;
	}
	
	protected boolean containsSpider() {
		if (included.size() == 0 || included.get(0).boxes.size() != 1)
			return false;
		ArrayList<Spider> spiders = included.get(0).boxes.get(0).spiders.list();
		for (int i = 0; i < spiders.size(); i++) {
			ArrayList<Point> points = spiders.get(i).points.list();
			for (int j = 0; j < points.size(); j++) {
				if (points.get(j).circles.size() == included.size() && included.containsAll(points.get(j).circles))
					return true;
			}
		}
		return false;
	}
	
	private void computeIncluded(Circle[] circles) {
		for (int i = 0; i < circles.length; i++) {
			if (circles[i].contains(freeform))
				included.add(circles[i], circles[i].shadings);
		}
 	}
	
	@Override
	public boolean intersects(Line line) {
		ArrayList<Circle> excluded = getExcluded();
		if (box.get() != null) {
			if (!box.get().contains(line))
				return false;
		} else if (included.size() > 0) {
			for (int i = 0; i < included.size(); i++) {
				if (!included.get(i).contains(line))
					return false;
			}
			
		} else {
			return false;
		}
		if (excluded != null) {
			for (int i = 0; i < excluded.size(); i++) {
				if (excluded.get(i).contains(line) || excluded.get(i).intersects(line))
					return false;
			}
		}
		return true;
	}
	
	@Override
	public void remove() {
		included.removeAll();
		box.set(null, null);
	}

	@Override
	public void draw(Graphics2D g2) {
		if (isValid()) {
			g2.setComposite(AlphaComposite.getInstance(AlphaComposite.SRC_OVER, 0.2f));
	    	g2.setColor(Color.BLUE);
			Box box;
			if (this.box.get() != null) {
				box = this.box.get();
			} else {
				box = included.get(0).boxes.get(0);
			}
			Area area = new Area(new Rectangle(box.topLeft.x, box.topLeft.y, box.width, box.height));
			for (int i = 0; i < included.size(); i++) {
				Circle circle = included.get(i);
				area.intersect(new Area(new Ellipse2D.Float(circle.center.x-circle.radius, circle.center.y-circle.radius, circle.radius*2, circle.radius*2)));
			}
			ArrayList<Circle> excluded = getExcluded();
			if (excluded != null) {
				for (int i = 0; i < excluded.size(); i++) {
					Circle circle = excluded.get(i);
					area.subtract(new Area(new Ellipse2D.Float(circle.center.x-circle.radius, circle.center.y-circle.radius, circle.radius*2, circle.radius*2)));
				}
			}
			g2.fill(area);
		    g2.setComposite(AlphaComposite.getInstance(AlphaComposite.SRC_OVER, 1));
		    g2.setColor(Color.BLACK);
		}
	}

	@Override
	public boolean isValid() {
		return (included.size() > 0 && included.get(0).boxes.size() == 1) || (box.get() != null);
	}
}
