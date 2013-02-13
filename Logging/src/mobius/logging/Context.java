/*
 * Software Engineering Tools.
 *
 * $Id: Context.jass,v 1.1.1.1 2002/12/29 12:36:10 kiniry Exp $
 *
 * Copyright (c) 1997-2001 Joseph Kiniry
 * Copyright (c) 2000-2001 KindSoftware, LLC
 * Copyright (c) 1997-1999 California Institute of Technology
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * - Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * - Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * - Neither the name of the Joseph Kiniry, KindSoftware, nor the
 * California Institute of Technology, nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS
 * IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL KIND SOFTWARE OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package mobius.logging;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

/**
 * <p> Context is the data structure that holds the information that is
 * relevant to debugging on a per-thread and a per-thread group basis. </p>
 *
 * <p> Each thread within a program is either in a debugging state or it is
 * not.  To signal that it is in the debugging state, that thread should do
 * the following (perhaps in an initDebug() method):
 *
 * <ol>
 * <li> Create a new Context object for that thread.  E.g.  <code>Context
 * debugContext = new Context();</code> All of the following method calls
 * are applied to this object, unless otherwise noted. </li>
 *
 * <li> Call the <code>turnOn();</code> to turn debugging on for this
 * thread. </li>
 *
 * <li> Add any new debugging categories specific to that thread with one
 * or more of the <code>addCategory()</code> methods. </li>
 *
 * <li> If this thread is only interested in the debugging output from a
 * specific set of classes, the <code>addClass()</code> methods can be used
 * to specify specific methods of interest.  Note that you'll likely want
 * to prefix the series of "class additions" with a
 * <code>removeClass(Thread.currentThread(), "*");</code> to flush the
 * context of the class narrowing/widening. </li>
 *
 * <li> Set the debug level that the thread is interested in with one of
 * the <code>setLevel()</code> methods. </li>
 * </ol>
 *
 * </p>
 *
 * <p> Now your thread has a valid debugging context, encapsulated in
 * its Context object.  This object is then passed to the Debug class
 * via the <code>addContext()</code> method so that the debugging
 * runtime system knows the threads context. </p>
 *
 * @version alpha_1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Debug
 * @see DebugConstants
 *
 * @design Most of this class used to be called PerDebugElement and
 * was used in package versions 0.01 through 0.17.
 * @design changeonly{} specifications are not used here because the
 * clone() method is part of the mobius.logging context design and is not
 * implemented for change only semantics.
 */
//+@ nullable_by_default
public class Context
  implements Cloneable, Serializable
{
  // Attributes

  /**
   * <p> This class contains several core instance variables:
   *
   * <ol>
   * <li> <code>isOn</code> is a boolean that indicates if debugging for
   * this element (thread or thread group) is turned on. </li>
   *
   * <li> <code>level</code> is an integer that indicates the current
   * debugging level for this element.  Its value ranges from
   * <code>LEVEL_MIN</code> to <code>LEVEL_MAX</code> of the current
   * installed <code>DebugConstantInterface</code>. </li>
   *
   * <li> <code>categoryMap</code> is a map containing
   * information on all categories defined in this debugging context and
   * their severity levels.  A key of this map is the category (type
   * <code>String</code>), while the data value is an <code>Integer</code>
   * representing the severity level of the category. </li>
   *
   * <li> <code>classMap</code> is a map containing information
   * on all classes that have debugging enabled or disabled in this
   * context.  A key of this map is the <code>String</code>
   * representation of a class (<code>Class.getName()</code>), while a data
   * value is a <code>Boolean</code> indicating if the given class has
   * debugging enabled. </li>
   * </ol>
   * </p>
   *
   * <p> Context objects are stored in the class-global per-thread and
   * per-thread group maps of the <code>Debug</code> class, keyed on
   * references to the thread or thread group, respectively. </p>
   */

  /**
   * A default UID.
   * @review kiniry Put in real UIDs?
   */
  private static final long serialVersionUID = 1L;

  /**
   * @serial The debugging constants for this class.
   */
  private transient final /*@ non_null spec_public @*/ DebugConstants my_debug_constants;

  /**
   * @serial A flag indicating if debugging is enabled for this
   * context.  If (isOn == false), all Debug calls like assert() and
   * print(), but for the query and state change functions (like
   * isOn(), turnOn(), etc.), are short-circuited and do nothing.
   */
  private /*@ spec_public @*/ volatile boolean my_is_on /*#guarded_by this*/;

  /**
   * @serial The current debug level of this context.
   * @design Higher valued levels usually indicate higher priorities.
   * E.g. A level 9 message is in the default implementation an assertion;
   * if it fails, the program exits.  A level 5 message is an error and the
   * user should probably be informed of the problem.  You can override
   * this behavior by subtyping DebugConstants and installing the new
   * constant during the construction of a Context.
   */
  private /*@ spec_public @*/ volatile int my_level /*#guarded_by this*/;
  //@ invariant validLevel(my_level);

  /**
   * @serial A map that binds category keys (Strings) to levels
   * (Integers).
   */
  private final /*@ non_null spec_public @*/ Map my_category_map /*#guarded_by this*/;

  /**
   * @serial A map that binds class names (Strings) to enable flags
   * (Booleans).
   */
  private final /*@ non_null spec_public @*/ Map my_class_map /*#guarded_by this*/;

  /**
   * The thread or thread group that owns this context.
   */
  private transient /*@ non_null spec_public @*/ Object my_owner /*#guarded_by this*/;

  /**
   * <p> The object used by this thread to control debugging output device.
   * All debugging messages that come from the owning thread will use this
   * output interface. </p>
   */
  private transient /*@ spec_public @*/ DebugOutput my_debug_output_interface;

  /**
   * <p> The constructor initializes all the static data-structures used by
   * the Context class.  Note that the <code>initCategories()</code> method
   * is automatically called as necessary to initialize the default
   * categories database of the Context class. </p>
   * 
   * <p> The context is associated with a thread or a thread group, but not
   * both. Therefore, one of the parameters <code>thread</code> and
   * <code>thread_group</code> has to be null. </p>
   *
   * @concurrency CONCURRENT
   * @param some_debug_constants an implementation of the <code>DebugConstants</code> that
   * defines the semantics of this debug context.
   * @param a_debug_output an implementation of <code>DebugOutput</code> that defines
   * the semantics of debugging output.
   * @param thread thread associated with this context
   * @param thread_group thread group associated with this context
   */
  // @todo kiniry put fields in objectState and use datagroup in frame axiom
  //@ requires a_thread != null ==> a_thread_group == null;
  //@ requires a_thread_group != null ==> a_thread == null;
  //@ ensures my_is_on == false;
  //@ ensures my_level == my_debug_constants.LEVEL_MIN;
  //@ ensures validLevel(my_level);
  //@ ensures my_debug_output_interface != null;
  // @todo kiniry Change these postconditions into an initially assertion.
  public Context(final /*@ non_null @*/ DebugConstants some_debug_constants,
                 final /*@ non_null @*/ DebugOutput a_debug_output,
                 final Thread a_thread,
                 final ThreadGroup a_thread_group) {
    super();
    my_is_on = false;
    my_category_map = new HashMap();
    //@ set my_category_map.keyType = \type(String);
    //@ set my_category_map.elementType = \type(Integer);
    //@ set my_category_map.removeSupported = true;
    my_class_map = new HashMap();
    //@ set my_class_map.keyType = \type(String);
    //@ set my_class_map.elementType = \type(Boolean);
    //@ set my_class_map.removeSupported = true;
    my_class_map.put("*", Boolean.TRUE);
    my_debug_constants = some_debug_constants;
    my_debug_constants.initCategories(my_category_map);
    my_level = DebugConstants.LEVEL_MIN;
    my_debug_output_interface = a_debug_output;
    my_owner = (a_thread != null) ? (Object)a_thread : (Object)a_thread_group;
  }

  /**
   * <p> The standard constructor.  The thread that is constructing the
   * context is the "owning thread".  All calls to this context will be
   * recognized only in the context of the original constructing
   * thread. </p>
   *
   * @concurrency CONCURRENT
   * @param some_debug_constants an implementation of the <code>DebugConstants</code> that
   * defines the semantics of this debug context.
   * @param a_debug_output an implementation of <code>DebugOutput</code> that defines
   * the semantics of debugging output.
   */
  // @todo kiniry put fields in objectState and use datagroup in frame axiom
  //@ ensures my_is_on == false;
  //@ ensures my_level == my_debug_constants.LEVEL_MIN;
  //@ ensures validLevel(my_level);
  //@ ensures my_debug_output_interface != null;
  //@ ensures my_owner != null;
  // @todo kiniry Change these postconditions into an initially assertion.
  public Context(final /*@ non_null @*/ DebugConstants some_debug_constants,
                 final /*@ non_null @*/ DebugOutput a_debug_output) {
	this( some_debug_constants, a_debug_output, Thread.currentThread(), null);
  }

  /**
   * <p> Constructs the thread-group context. The context is automatically
   * associated with every thread which belongs to the specified thread
   * group. </p>
   *
   * @concurrency CONCURRENT
   * @param some_debug_constants an implementation of the <code>DebugConstants</code> that
   * defines the semantics of this debug context.
   * @param a_debug_output an implementation of <code>DebugOutput</code> that defines
   * the semantics of debugging output.
   * @param thread_group thread group associated with this context
   */
  // @todo kiniry put fields in objectState and use datagroup in frame axiom
  //@ ensures my_is_on == false;
  //@ ensures my_level == my_debug_constants.LEVEL_MIN;
  //@ ensures validLevel(my_level);
  //@ ensures my_debug_output_interface != null;
  //@ ensures my_owner != null;
  // @todo kiniry Change these postconditions into an initially assertion.
  public Context(final /*@ non_null @*/ DebugConstants some_debug_constants,
                 final /*@ non_null @*/ DebugOutput a_debug_output,
                 final /*@ non_null @*/ ThreadGroup a_thread_group) {
	this( some_debug_constants, a_debug_output, null, a_thread_group);
  }

  /**
   * <p> Used to clone a Context for another thread.  Should be called
   * <em>only</em> by the thread that is going to use/modify the
   * context. </p>
   *
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the clone of the Context.
   * @throws CloneNotSupportedException never.
   */
  public /*@ non_null @*/ Object clone() throws CloneNotSupportedException {
    Context a_context_clone = null;
    try {
      a_context_clone = (Context)super.clone();
      //@ assume \fresh(a_context_clone);
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
    a_context_clone.my_owner = Thread.currentThread();
    a_context_clone.my_debug_output_interface = my_debug_output_interface;

    return a_context_clone;
  }

  /**
   * 
   * @return the thread that owns this context or null if it is owned with
   * a thread group
   *
   * @concurrency CONCURRENT
   * @modifies QUERY
   */
  //@ ensures \result == my_owner;
  //@ ensures \result != null;
  public /*@ pure @*/ Object getOwner() {
    return my_owner;
  }

  /**
   * <p> Turns on debugging facilities for the owner thread.  Note that if
   * you do not <code>turnOff()</code> debugging for this thread before it
   * becomes in active in the system, it will not be garbage collected,
   * since it is referenced by the Context object. </p>
   *
   * @concurrency GUARDED
   */
  //@ assignable my_is_on;
  //@ ensures my_is_on;
  public void turnOn() {
    my_is_on = true;
  }

  /**
   * <p> Turns off debugging facilities for the owner thread.  Note that if
   * you do not <code>turnOff</code> debugging for this thread before it
   * becomes in active in the system, it will not be garbage collected,
   * since it is referenced by the Context object. </p>
   *
   * @concurrency GUARDED
   * @review Create a garbage collection thread for Debug to clean up dead
   * threads?
   */
  //@ assignable my_is_on;
  //@ ensures !my_is_on;
  public void turnOff() {
    my_is_on = false;
  }

  /**
   * @concurrency GUARDED
   * @modifies QUERY
   * @return a boolean indicating if any debugging is turned on.
   */
  //@ ensures \result == my_is_on;
  public /*@ pure @*/ boolean isOn() {
    return my_is_on;
  }

  /**
   * <p> Adds a category to the database of legal debugging categories for
   * the owner thread.  Once a category exists in the database, its
   * debugging level cannot be changed without removing and re-adding the
   * category to the database. </p>
   *
   * @concurrency GUARDED
   * @modifies categoryMap
   * @param a_category the category to add to the global set of categories.
   * @param a_level the debugging level associated with the passed category.
   * @return a boolean indicating if the category was successfully added to
   * the database.  A false indicates either the category was already in
   * the database at a different level or the parameters were invalid.
   */
  //@ requires a_category.length() > 0;
  //@ requires validLevel(a_level);
  //@ ensures containsCategory(a_category);
  public synchronized boolean addCategory(final /*@ non_null @*/ String a_category,
                                          final int a_level) {
    // See if an entry for the passed category exists.
    if (my_category_map.containsKey(a_category)) {
      final Integer a_Level = (Integer)my_category_map.get(a_category);
      //@ assume a_Level != null;
      return a_Level.intValue() == a_level;
    }

    // Add a new entry for the passed category.
    my_category_map.put(a_category, Integer.valueOf(a_level));

    return true;
  }

  /**
   * <p> Removes a category from the database of legal debugging categories
   * for the owner thread. </p>
   *
   * @concurrency GUARDED
   * @param a_category the category to remove.
   * @return a boolean indicating if the category was successfully
   * removed from the database.  A false indicates that the parameters
   * were invalid.
   */
  //@ requires a_category.length() > 0;
  //@ ensures !containsCategory(a_category);
  public synchronized boolean removeCategory(final /*@ non_null @*/ String a_category) {
    // If it is in the map, remove it.
    if (my_category_map.containsKey(a_category)) {
      my_category_map.remove(a_category);
      return true;
    } else return false;
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @param a_category is the category to lookup.
   * @return a boolean indicating if a category is in the class-global
   * category database.
   */
  //@ requires a_category.length() > 0;
  public synchronized /*@ pure @*/ boolean
  containsCategory(final /*@ non_null @*/ String a_category) {
    return my_category_map.containsKey(a_category);
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @param a_category is the category to lookup.
   * @return the level of the category provided it is in the category
   * database of this context.
   */
  //@ requires a_category.length() > 0;
  //@ requires containsCategory(a_category);
  public synchronized /*@ pure @*/ int getCategoryLevel(final /*@ non_null @*/ String a_category) {
    return ((Integer)(my_category_map.get(a_category))).intValue();
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @return a vector that contains all the per-thread or per-thread group
   * debugging categories that are currently in this Context's category
   * database.
   */
  public synchronized /*@ pure non_null @*/ Vector listCategories() {
    return new Vector( my_category_map.values());
  }

  /**
   * @return a boolean indicating that this Context's database of classes
   * contains the specified class.
   *
   * @modifies QUERY
   * @concurrency GUARDED
   * @param the_class_name the name of the class to check.
   */
  //@ requires 0 < the_class_name.length();
  public synchronized /*@ pure @*/ boolean
  containsClass(final /*@ non_null @*/ String the_class_name) {
    return my_class_map.containsKey(the_class_name);
  }

  /**
   * @return a boolean indicating that this Context's database of classes
   * contains the specified class.
   *
   * @modifies QUERY
   * @concurrency GUARDED
   * @param the_class_ref the class to check.
   */
  //@ requires 0 < the_class_ref.getName().length();
  public synchronized /*@ pure @*/ boolean
  containsClass(final /*@ non_null @*/ Class the_class_ref) {
    return containsClass(the_class_ref.getName());
  }

  /**
   * <p> Adds a class to this Context's database of classes that have
   * debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @param a_class_reference the class to add to the global table of classes
   * that have debugging enabled.
   */
  public synchronized void addClass(final /*@ non_null @*/ Class a_class_reference) {
    Utilities.addClassToMap(my_class_map, a_class_reference.getName());
  }

  /**
   * <p> Adds a class to this Context's database of classes that have
   * debugging enabled. Note that a class of "*" means that all classes
   * will now have debugging enabled for the owning thread.  There is no
   * way to "undo" such a command short of manually adding the individual
   * classes back to the database. (Or, equivalently, removing the
   * complement.) </p>
   *
   * @concurrency GUARDED
   * @param a_class_name the name of the class to add.
   */
  //@ requires a_class_name.length() > 0;
  public synchronized void addClass(final /*@ non_null @*/ String a_class_name) {
    Utilities.addClassToMap(my_class_map, a_class_name);
  }

  /**
   * <p> Removes a class from this Context's database of classes that have
   * debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @param a_class_reference the class to remove from this Context's table of
   * classes that have debugging enabled.
   */
  public synchronized void removeClass(final /*@ non_null @*/ Class a_class_reference) {
    Utilities.removeClassFromMap(my_class_map, a_class_reference.getName());
  }

  /**
   * <p> Removes a class from this Context's database of classes that have
   * debugging enabled.  Note that a class of "*" means that all classes
   * will be removed and debugging disabled.  There is no way to "undo"
   * such a command. </p>
   *
   * @concurrency GUARDED
   * @param a_class_name the class to remove from this Context's table of
   * classes that have debugging enabled.
   */
  //@ requires a_class_name.length() > 0;
  public synchronized void removeClass(final /*@ non_null @*/ String a_class_name) {
    Utilities.removeClassFromMap(my_class_map, a_class_name);
  }

  /**
   * <p> Returns a <code>Vector</code> that contains all the classes that have
   * debugging enabled in this Context. </p>
   *
   * @modifies QUERY
   * @concurrency GUARDED
   * @return a vector that contains all the classes that
   * currently have debugging enabled (they are in the class database)
   * for the owning thread or thread group.
   */
  public synchronized /*@ non_null pure @*/ Vector listClasses() {
    return new Vector( my_class_map.values());
  }

  /**
   * <p> Set a new debugging level for the owning thread. </p>
   *
   * @concurrency GUARDED
   * @param the_new_level the new debugging level.
   */
  //@ requires validLevel(the_new_level);
  //@ assignable my_level;
  //@ ensures getLevel() == the_new_level;
  //@ ensures validLevel(my_level);
  public void setLevel(final int the_new_level) {
    my_level = the_new_level;
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @return the current debugging level for the owning thread.
   */
  //@ ensures validLevel(\result);
  //@ ensures \result == my_level;
  public /*@ pure @*/ int getLevel() {
    return my_level;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>DebugOutput</code> for the owning thread.
   */
  public /*@ pure @*/ DebugOutput getOutputInterface() {
    return my_debug_output_interface;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return a flag indicating if the provided level is valid.
   * @param a_level the level to check.
   */
  //@ ensures \result == ((a_level >= my_debug_constants.LEVEL_MIN) && (a_level <= my_debug_constants.LEVEL_MAX));
  public /*@ pure @*/ boolean validLevel(final int a_level) {
    return ((a_level >= DebugConstants.LEVEL_MIN) &&
            (a_level <= DebugConstants.LEVEL_MAX));
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class Context

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
