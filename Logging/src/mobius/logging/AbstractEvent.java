/*
 * Software Engineering Tools.
 *
 * $Id: Event.jass,v 1.1.1.1 2002/12/29 12:36:15 kiniry Exp $
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
import java.util.Date;

/**
 * <p> AbstractEvent is a utility base class from which all log/monitoring events
 * can derive or have embedded. </p>
 *
 * @version alpha-1
 * @author Joseph Kiniry (kiniry@acm.org)
 * @bon Represents a single important event of any kind. The event includes
 * a source, description, importance, and time, among other things.
 *
 * @concurrency (CONCURRENT) All methods are getters, thus there are no
 * concurrency issues.
 * @modifies (SINGLE-ASSIGNMENT-FIELDS) All attributes are set only on
 * construction.
 * @modifies (QUERY-METHODS) All methods are functions.
 *
 * @design The class invariants covers the legal values of all attributes,
 * thus no values tag is necessary in the specification.
 * @design Events cannot be cloned.
 */
//+@ nullable_by_default
public abstract class AbstractEvent extends Object
  implements Event, Serializable, Cloneable {
  // Attributes

  /** Standard serial version ID. */
  private static final long serialVersionUID = 1L;

  /**
   * The source host for this event.
   *
   * @see #getSourceHost
   * @example sourceHost = "joe.kindsoftware.com"
   */
  private final /*@ non_null @*/ String my_source_host;

  /**
   * The source component for this event.
   *
   * @see #getSourceComponent
   * @example sourceComponent = "Monitoring System, version 0.1.0"
   */
  private final /*@ non_null @*/ String my_source_component;

  /**
   * The date on which this event was created.
   *
   * @see #getCreationDate
   */
  private final /*@ non_null @*/ Date my_creation_date;

  /**
   * The text description of this event.
   *
   * @see #getDescription
   * @example description = "Available memory is beneath 1.0 MB."
   */
  private final /*@ non_null @*/ String my_description;

  /**
   * The "type" of this event.
   *
   * @see #getType
   * @example type = "MEMORY_WARNING"
   */
  private final /*@ non_null @*/ String my_type;

  /**
   * The "level" of this event.
   *
   * @see #getLevel
   * @see DebugConstants
   * @example level = debugConstants.WARNING
   */
  private final int my_level;

  // Constructors

  /**
   * <p> This the standard constructor for Event.  No other constructor can
   * be legally used. </p>
   *
   * @param the_source_host The source host for the event.
   * @param the_source_component The source component for the event.
   * @param the_description An English description of the event.
   * @param the_event_type The type of the event.
   * @param the_event_level The level of the event.
   *
   * @bon Create a new event with the following specification.
   * @ensures Result.getCreationDate() returns a time that is between the
   * time in which this method is called and it returns.
   * @generates A new, valid instance of Event.
   */
  //@ ensures getSourceHost().equals(the_source_host);
  //@ ensures getSourceComponent().equals(the_source_component);
  //@ ensures getCreationDate() != null;
  //@ ensures getDescription().equals(the_description);
  //@ ensures getType().equals(the_event_type);
  //@ ensures getLevel() == the_event_level;
  public AbstractEvent(final /*@ non_null @*/ String the_source_host,
                       final /*@ non_null @*/ String the_source_component,
                       final /*@ non_null @*/ String the_description,
                       final /*@ non_null @*/ String the_event_type,
                       final int the_event_level) {
    super();
    this.my_source_host = the_source_host;
    this.my_source_component = the_source_component;
    this.my_creation_date = new Date();
    this.my_description = the_description;
    this.my_type = the_event_type;
    this.my_level = the_event_level;
  }

  // Inherited methods

  /**
   * <p> What is a printable representation of this event? </p>
   *
   * @ensures Result = "[short-date/time-form | sourceHost |
   *                     sourceComponent] type : level -\n\tDescription"
   * @overrides java.lang.Object.toString()
   * @return a printable representation of the event.
   * @complexity O(1) - Note that String catenation is very expensive, so
   * use this method sparingly.  Also, the length of the output is directly
   * proportional to the event description.
   */
  public /*@ pure non_null @*/ String toString() {
    return "[" + my_creation_date.toString() + " | " + my_source_host + " | " +
      my_source_component + "] " + my_type + ":" + my_level + " - " + my_description;
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ int hashCode() {
    return
      my_source_host.hashCode() +
      my_source_component.hashCode() +
      my_creation_date.hashCode() +
      my_description.hashCode() +
      my_type.hashCode() +
      my_level;
  }

  /**
   * <p> Is this event equal to another one? </p>
   *
   * @param an_object the event with which to compare.
   * @return if two AbstractEvents are equal.
   * @ensures (Result == true) iff
   *          (for_all attributes of Event : attributes of the objects
   *          being compared have identical values)
   * @overrides java.lang.Object.equals()
   */
  public boolean equals(final Object an_object) {
    if (an_object instanceof AbstractEvent) {
      final AbstractEvent an_event = (AbstractEvent)an_object;
      return (my_source_host.equals(an_event.getSourceHost()) &&
       my_source_component.equals(an_event.getSourceComponent()) &&
       my_creation_date.equals(an_event.getCreationDate()) &&
       my_description.equals(an_event.getDescription()) &&
       my_type.equals(an_event.getType()) && my_level == an_event.getLevel());
    } else return false;
  }

  /** {@inheritDoc} */
  public /*@ non_null */ Object clone() throws CloneNotSupportedException {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  // Public Methods

  /** {@inheritDoc} */
  public /*@ pure @*/ String getSourceHost() {
    return my_source_host;
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ String getSourceComponent() {
    return my_source_component;
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ Date getCreationDate() {
    return (Date)(my_creation_date.clone());
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ String getDescription() {
    return my_description;
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ String getType() {
    return my_type;
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ int getLevel() {
    return my_level;
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class AbstractEvent

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
