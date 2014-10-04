package spiderdrawer;

import java.util.ArrayList;

public class ActionManager {

	private ArrayList<Action> actionList;
	int current;
	
	public ActionManager() {
		actionList = new ArrayList<Action>();
	}
	
	public synchronized void add(Action action) {
		while (actionList.size() > current) 
			actionList.remove(actionList.size()-1);
		actionList.add(action);
		current = actionList.size();
	}
	
	public synchronized void undo() {
		current--;
		actionList.get(current).undo();
	}
	
	public synchronized void redo() {
		actionList.get(current).redo();
		current++;
	}
	
	public synchronized boolean canUndo() {
		return (actionList.size() > 0 && current != 0); 
	}
	
	public synchronized boolean canRedo() {
		return (actionList.size() > 0 && current < actionList.size()); 
	}
	
}
