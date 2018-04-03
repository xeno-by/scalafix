package scalafix
package internal.util

import scala.collection.mutable
import scala.meta._
import scala.{meta => m}

case class EagerInMemorySemanticdbIndex(
    database: Database,
    sourcepath: Sourcepath,
    classpath: Classpath,
    table: SymbolTable = SymbolTable.empty
) extends SemanticdbIndex {
  override def toString: String =
    s"$productPrefix($sourcepath, $classpath, database.size=${database.documents.length})"
  override def hashCode(): Int = database.hashCode()
  private lazy val _denots: mutable.Map[Symbol, Denotation] = {
    val builder = mutable.Map.empty[Symbol, Denotation]
    database.symbols.foreach(r => builder += (r.symbol -> r.denotation))
    builder.result()
  }
  private lazy val _names: mutable.Map[Position, ResolvedName] = {
    val builder = mutable.Map.empty[Position, ResolvedName]
    def add(r: ResolvedName): Unit = {
      builder.get(r.position) match {
        case Some(conflict) =>
          conflict.symbol match {
            case m.Symbol.Multi(syms) =>
              builder(r.position) =
                conflict.copy(symbol = m.Symbol.Multi(r.symbol :: syms))
            case sym =>
              builder(r.position) =
                conflict.copy(symbol = m.Symbol.Multi(r.symbol :: sym :: Nil))
          }
        case _ =>
          builder(r.position) = r
      }
    }
    database.documents.foreach { entry =>
      entry.names.foreach(add)
      entry.synthetics.foreach(_.names.foreach(add))
      entry.symbols.foreach(_.denotation.names.foreach(add))
    }
    builder.result()
  }
  def symbol(position: Position): Option[Symbol] =
    _names.get(position).map(_.symbol)
  def symbol(tree: Tree): Option[Symbol] = tree match {
    case name @ Name(_) =>
      val syntax = name.syntax
      // workaround for https://github.com/scalameta/scalameta/issues/1083
      val pos =
        if (syntax.startsWith("(") &&
          syntax.endsWith(")") &&
          syntax != name.value)
          Position.Range(name.pos.input, name.pos.start + 1, name.pos.end - 1)
        else name.pos
      symbol(pos)
    case Importee.Rename(name, _) => symbol(name)
    case Importee.Name(name) => symbol(name)
    case Term.Select(_, name @ Name(_)) => symbol(name)
    case Type.Select(_, name @ Name(_)) => symbol(name)
    case _ => symbol(tree.pos)
  }
  def denotation(symbol: Symbol): Option[Denotation] =
    _denots.get(symbol)
  def denotation(tree: Tree): Option[Denotation] =
    symbol(tree).flatMap(denotation)
  override def names: Seq[ResolvedName] = _names.values.toSeq
  def withDocuments(documents: Seq[Document]): SemanticdbIndex =
    copy(database = Database(documents))
}
