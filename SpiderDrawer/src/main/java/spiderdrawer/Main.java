package spiderdrawer;

import spiderdrawer.ui.MainForm;

public class Main {

	static Object[] array;
	
	public static void main(String[] args) {
            System.setProperty("apple.laf.useScreenMenuBar", "true");
            System.setProperty("com.apple.mrj.application.apple.menu.about.name", "Spider Drawer");
            MainForm.main(args);
	}
	
}
