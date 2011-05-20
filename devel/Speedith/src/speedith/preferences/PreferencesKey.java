/*
 *   Project: Speedith
 * 
 * File name: PreferencesKey.java
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
package speedith.preferences;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The field (of type {@code static final String}) annotated with this
 * annotation specifies a {@link java.util.prefs.Preferences#keys() preferences
 * key} from the {@link java.util.prefs.Preferences Preferences API}.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.FIELD)
public @interface PreferencesKey {
    /**
     * The description of the {@link java.util.prefs.Preferences#keys()
     * preferences key} the field annotated with this annotation is referring
     * to.
     * @return description of the {@link java.util.prefs.Preferences#keys()
     * preferences key} the field annotated with this annotation is referring
     * to.
     */
    String description();
    /**
     * The class' package in which this preference is stored.
     * <p>The default value is {@code void.class}.</p>
     * @return the class' package in which this preference is stored.
     */
    Class<?> inPackage() default void.class;
    /**
     * Indicates whether the preference is user specific or system-wide.
     * <p>Default is {@code true}.</p>
     * @return a value that indicates whether the preference is user specific or
     * system-wide.
     */
    boolean isUserPreference() default true;
}
