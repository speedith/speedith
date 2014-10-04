package spiderdrawer;

import java.util.ArrayList;

import spiderdrawer.shape.Point;
import spiderdrawer.shape.Shading;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;

public class Action {
	
	private enum ActionType {
        NULL, MOVE, DELETE, CREATE;
    }
	
	private ArrayList<Shape> shapeList;
	private ActionType type;
	private Movable mShape;
	private Point from;
	private Point to;
	private ArrayList<Deletable> deleted;
	private Shape created;
	private boolean undid = false;
	
	public Action(ArrayList<Shape> shapeList) {
		this.shapeList = shapeList;
		type = ActionType.NULL;
	}
	
	public boolean isDelete() {
		return type == ActionType.DELETE;
	}
	
	public void setMove(Movable mShape, Point from, Point to) {
		type = ActionType.MOVE;
		this.mShape = mShape;
		this.from = from;
		this.to = to;
	}
	
	public void setDelete() {
		type = ActionType.DELETE;
		this.deleted = new ArrayList<Deletable>();
	}
	
	public void add(Deletable deleted) {
		this.deleted.add(deleted);
	}
	
	public void setCreate(Shape created) {
		type = ActionType.CREATE;
		this.created = created;
	}
	
	public void undo() {
		if (undid)
			return;
		switch (type) {
			case MOVE: undoMove(); break;
			case DELETE: undoDelete(); break;
			case CREATE: undoCreate(); break;
			default: break;
		}
		undid = true;
		
	}
	
	public void redo() {
		if (!undid)
			return;
		switch (type) {
			case MOVE: redoMove(); break;
			case DELETE: redoDelete(); break;
			case CREATE: redoCreate(); break;
			default: break;
		}
		undid = false;
	}
	
	private void undoMove() {
		mShape.move(to, from);
		mShape.recompute(false);
	}
	
	private void undoDelete() {
		shapeList.addAll(deleted);
		for (int i = 0; i < deleted.size(); i++)
			if (deleted.get(i) instanceof Movable)
				((Movable) deleted.get(i)).recompute(false);
			else if (deleted.get(i) instanceof Shading)
				((Shading) deleted.get(i)).compute();
	}
	
	private void undoCreate() {
		shapeList.remove(created);
		if (created instanceof Deletable)
			((Deletable) created).remove();
	}
	
	private void redoMove() {
		mShape.move(from, to);
		mShape.recompute(false);
	}
	
	private void redoDelete() {
		shapeList.removeAll(deleted);
		for (int i = 0; i < deleted.size(); i++) {
			shapeList.remove(deleted.get(i));
			deleted.get(i).remove();
		}
	}
	
	private void redoCreate() {
		shapeList.add(created);
		if (created instanceof Movable)
			((Movable) created).recompute(false);
		else if (created instanceof Shading)
			((Shading) created).compute();
	}
	
}
