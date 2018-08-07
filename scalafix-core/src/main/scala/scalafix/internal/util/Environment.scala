package scalafix.internal.util

import scala.meta.internal.semanticdb.TypeSignature
import scala.meta.{Defn, Import, Importee, Name, Pkg, Source, Stat, Template, Tree, Type}
import scala.meta.internal.semanticdb.{ClassSignature, TypeRef}
import scala.meta.internal.symtab.SymbolTable
import scalafix.v0.{SemanticdbIndex, Signature, Symbol}


object Environment {
  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Scopes
  //

  // Scope /////////////////////////////////////////////////////////////////////////////////////////

  trait Scope {
    /**
     * Resolve a Signature relative to this scope to an Option[Symbol]: if
     * there is a symbol in scope that has the name and kind in the given
     * signature, return it; otherwise, return None.
     *
     * @param signature
     * @return
     */
    def resolveSignature(signature: Signature): Option[Symbol]

    /**
     * If symbol is a type alias, iteratively expand the type alias to its
     * definition until we get to a symbol that is not a type alias. This
     * allows us to determine when two different symbols that are type aliases
     * actually refer to the same type.
     *
     * @param symbol
     * @return
     */
    def expandTypeAliases(symbol: Symbol): Symbol
  }

  // ExplicitImport and WildcardImport /////////////////////////////////////////////////////////////

  /**
   * The ExplicitImport case class is used to keep track of an explicit import
   * in AbstractScope and its subclasses. This supports renaming imports:
   * simply provide a Signature whose name is different from the imported Symbol.
   *
   * @param symbol Fully-qualified Symbol to import
   * @param signature Signature to import as (i.e., name + kind)
   */
  private final case class ExplicitImport(symbol: Symbol, signature: Signature)

  /**
   * The WildcardImport case class is used to keep track of wildcard import
   * in AbstractScope and its subclasses. This supports unimports, like:
   *   import java.io.{FileInputStream => _, _}
   * The example above means import everything except for FileInputStream
   * from the java.io package.
   *
   * @param symbol Fully-qualified Symbol for a package, object or class to
   *               import all contents from
   * @param unimports Names to not import
   */
  private final case class WildcardImport(symbol: Symbol, unimports: Set[Name] = Set.empty)

  // EmptyScope ////////////////////////////////////////////////////////////////////////////////////

  /**
   * EmptyScope can be used as a default case that is not able to resolve any
   * type signatures or expand any type aliases.
   */
  object EmptyScope extends Scope {
    override def resolveSignature(signature: Signature): Option[Symbol] = None
    override def expandTypeAliases(symbol: Symbol): Symbol = symbol
  }

  // AbstractScope /////////////////////////////////////////////////////////////////////////////////

  /**
   * AbstractScope is the base class for all our implementations of Scope.
   *
   * @param index SemanticdbIndex used to look up information about symbols
   * @param outerScopeOption is a reference to the outer scope that contains
   *                         this scope (if there is any)
   * @param scopeSymbol is the Symbol identifying this scope
   * @param explicitImports is the list of explicit imports directly in this scope
   * @param wildcardImports is the list of wildcard imports directly in this scope
   */
  private abstract class AbstractScope(
    protected val index: SemanticdbIndex,
    protected val outerScopeOption: Option[AbstractScope],
    protected val scopeSymbol: Symbol,
    protected val explicitImports: Seq[ExplicitImport] = Seq.empty,
    protected val wildcardImports: Seq[WildcardImport] = Seq.empty
  ) extends Scope {
    protected final def symbolTable: SymbolTable = index.asInstanceOf[SymbolTable]

    /**
     * Checks if a Symbol actually exists. Returns Some(symbol) if it exists,
     * or None if it does not exist.
     *
     * @param symbol
     * @return
     */
    protected final def checkSymbolExists(
      symbol: Symbol
    ): Option[Symbol] = {
      // TODO: Check that symbols are accessible from the current scope
      symbolTable
        .info(symbol.syntax)
        .map { symbolInfo => symbol }
    }

    final override def expandTypeAliases(
      symbol: Symbol
    ): Symbol = {
      symbolTable.info(symbol.syntax) match {
        case Some(symbolInfo) if symbolInfo.kind.isType => symbolInfo.signature match {
          case TypeSignature(_, TypeRef(_, lowerBoundSymbol, _), TypeRef(_, upperBoundSymbol, _))
            if lowerBoundSymbol == upperBoundSymbol => expandTypeAliases(Symbol(lowerBoundSymbol))
          case _ => symbol
        }
        case _ => symbol
      }
    }

    /**
     * Find a definition for signature directly in the current scope
     * (or inherited, but not coming from an import or an enclosing scope).
     *
     * This is a default implementation that may be overridden by a subclass.
     *
     * @param signature
     * @return
     */
    protected def matchingDefinitionFromCurrentScope(
      signature: Signature
    ): Option[Symbol] = {
      checkSymbolExists(Symbol.Global(scopeSymbol, signature))
    }

    /**
     * Find a definition for signature in the current scope (including
     * inherited by the current scope, but *not* coming from an import) or an
     * enclosing scope other than the top level of a source file.
     *
     * This is a default implementation that may be overridden by a subclass.
     * In particular, SourcePackage overrides this to return None, since it
     * describes a top-level scope.
     *
     * @param signature
     * @return
     */
    protected def matchingDefinitionFromAnyNonTopLevelScope(
      signature: Signature
    ): Option[Symbol] = {
      matchingDefinitionFromCurrentScope(signature)
        .orElse(outerScopeOption.flatMap(_.matchingDefinitionFromAnyNonTopLevelScope(signature)))
    }

    /**
     * Finds all explicit imports directly in the current scope that bind the
     * name signature, and returns the AbsoluteSymbols they bind it to.
     *
     * @param signature
     * @return
     */
    private def matchingExplicitImportsFromCurrentScope(
      signature: Signature
    ): Seq[Symbol] = {
      explicitImports.collect {
        case ExplicitImport(importSymbol, importSignature)
          if (importSignature == signature) =>
          importSymbol
      }.distinct
    }

    /**
     *
     * @param signature
     * @return
     */
    private def matchingExplicitImportsFromAnyScope(
      signature: Signature
    ): Seq[Symbol] = {
      matchingExplicitImportsFromCurrentScope(signature) ++
        outerScopeOption.toSeq.flatMap(_.matchingExplicitImportsFromAnyScope(signature))
    }

    final override def resolveSignature(
      signature: Signature
    ): Option[Symbol] = {
      // 1. A matching definition in the current scope (or inherited by the current scope)
      matchingDefinitionFromCurrentScope(signature) match {
        case m @ Some(_) => m
        case None =>
          // 2. A matching explicit import in the current scope, unless there is an
          //    ambiguity due to (a) more than one such, or (b) a matching definition
          //    at an outer scope
          matchingExplicitImportsFromCurrentScope(signature) match {
            case _::_::_ => None  // Multiple ambiguous explicit imports
            case importedSymbol::Nil =>
              val competitorSymbols = importedSymbol +:
                outerScopeOption.toSeq.flatMap {
                  _.matchingDefinitionFromAnyNonTopLevelScope(signature)
                }
              competitorSymbols.distinct match {
                case uniqueSymbol::Nil => Some(uniqueSymbol)
                case _::_::_ => None
              }
            case Nil =>
              // 3. A matching wildcard import in the current scope, unless there is an
              //    ambiguity due to (a) more than one such, (b) a matching definition
              //    at an outer scope, or (c) a matching explicit import at an outer scope
              val matchingWildcardImportsFromCurrentScope = wildcardImports.flatMap {
                case WildcardImport(importPackageSymbol, unimportedNames) =>
                  if (unimportedNames.exists(_.value == signature.name)) {
                    None
                  } else {
                    checkSymbolExists(Symbol.Global(importPackageSymbol, signature))
                  }
              }.distinct
              matchingWildcardImportsFromCurrentScope match {
                // TODO: make sure our choice amongst wildcard imports works correctly
                // TODO: for some reason "List#" doesn't resolve while "Map#" does, due to what aliases scala.Predef does and doesn't define
//                case _::_::_ => None
                case importedSymbol::_ =>
                  val competitorSymbols = importedSymbol +:
                    (outerScopeOption.toSeq.flatMap {
                      _.matchingDefinitionFromAnyNonTopLevelScope(signature)
                    } ++
                    outerScopeOption.toSeq.flatMap{
                      _.matchingExplicitImportsFromAnyScope(signature)
                    })
                  competitorSymbols.distinct match {
                    case uniqueSymbol::Nil => Some(uniqueSymbol)
                    case _::_::_ => None
                  }
                case Nil =>
                  // 4. Recurse to outer scope
                  outerScopeOption.flatMap(_.resolveSignature(signature))
              }
          }
      }
    }
  }

  // SourceFileScope //////////////////////////////////////////////////////////////////////////////////

  /**
   * SourceFileScope is the concrete base case of Scope, used to represent what
   * is in scope at the top level of a source file, outside of the bodies of any
   * particular classes/objects/traits.
   *
   * To be clear: There is not just a single instance of SourceFileScope for a
   * given source file. Each instance corresponds to the imports that are in
   * scope at a specific position at the top level of a source file.
   *
   * @param index
   * @param scopeSymbol
   */
  private final class SourceFileScope(
    index: SemanticdbIndex,
    scopeSymbol: Symbol,
    explicitImports: Seq[ExplicitImport],
    wildcardImports: Seq[WildcardImport]
  ) extends AbstractScope(index, None, scopeSymbol, explicitImports, wildcardImports) {
    override protected def matchingDefinitionFromAnyNonTopLevelScope(
      signature: Signature
    ): Option[Symbol] = None
  }

  private object SourceFileScope {
    // TODO: This is not 100% equivalent to what scalac does. With scalac, if
    // a source file includes some imports of scala.Predef at the top level,
    // then the default import of scala.Predef is disabled.
    val DefaultWildcardImport: Seq[WildcardImport] =
      Seq(WildcardImport(Symbol("")),
        WildcardImport(Symbol("java/lang/")),
        WildcardImport(Symbol("scala/")),
        WildcardImport(Symbol("scala/package.")),
        WildcardImport(Symbol("scala/Predef.")))

    def apply(
      index: SemanticdbIndex,
      scopeSymbol: Symbol,
      explicitImports: Seq[ExplicitImport],
      wildcardImports: Seq[WildcardImport]
    ): SourceFileScope = new SourceFileScope(index, scopeSymbol, explicitImports,
      DefaultWildcardImport ++ wildcardImports)

    /**
     * Returns a SourceFileScope that's not in any package and doesn't have
     * any explicit imports, but is still able to query the symbol table and
     * look up default imports.
     *
     * @param index
     * @return
     */
    def notInAnyPackage(index: SemanticdbIndex): SourceFileScope =
      SourceFileScope(index, Symbol.None, Seq.empty, DefaultWildcardImport)
  }

  // TemplateScope /////////////////////////////////////////////////////////////////////////////////

  /**
   * TemplateScope represents the Scope within a class/object/trait body.
   *
   * @param index
   * @param outerScope
   * @param scopeSymbol
   */
  private final class TemplateScope(
    index: SemanticdbIndex,
    outerScope: AbstractScope,
    scopeSymbol: Symbol,
    typeParameters: Set[Signature.TypeParameter],
    explicitImports: Seq[ExplicitImport],
    wildcardImports: Seq[WildcardImport]
  ) extends AbstractScope(
      index, Some(outerScope), scopeSymbol, explicitImports, wildcardImports) {
    /**
     * inheritanceOrder is a list of template AbsoluteSymbols in the order
     * in which to check them for definitions that are in scope. The first
     * element in the list is this template, followed by templates it
     * inherits from, in the order defined by Scala's inheritance rules.
     *
     * The general approach is:
     *   Definitions in this template itself take first priority
     *   Otherwise look for the template introduced latest in the inheritance
     *     graph that provides a matching definition
     *
     * For example:
     *   trait A { def x = "A" }
     *   trait B extends A { override def x = "B" }
     *   trait C extends A { override def x = "C" }
     *   trait D extends A { override def x = "D" }
     *   trait E extends B with C
     *   trait F extends D with C
     *   object G extends E with F
     *   G.x // => "D"
     * Hence for G, inheritanceOrder is ["G.", "F#", "D#", "E#", "C#", "B#", "A#", "AnyRef#", "Any#"]
     */
    private val inheritanceOrder = {
      def recurse(templateSymbol: Symbol): Seq[Symbol] = {
        symbolTable
          .info(templateSymbol.syntax).get
          .signature.asInstanceOf[ClassSignature]
          .parents.map {
            parent => Symbol(parent.asInstanceOf[TypeRef].symbol)
          }.flatMap(recurse) :+ templateSymbol
      }
      recurse(scopeSymbol)
        .distinct
        .reverse
    }

    /**
     * Find a definition for symbolComponent directly in the current scope
     * (or inherited, but not coming from an import or an enclosing scope).
     *
     * @param signature
     * @return
     */
    override protected def matchingDefinitionFromCurrentScope(
      signature: Signature
    ): Option[Symbol] = {
      signature match {
        // Type termParameters are a special case because they are not inherited.
        case typeParameter: Signature.TypeParameter =>
          if (typeParameters.contains(typeParameter))
            Some(Symbol.Global(scopeSymbol, typeParameter))
          else
            None
        case _ =>
          // TODO: check that inherited symbols are non-private
          inheritanceOrder
            .map { Symbol.Global(_, signature) }
            .find { checkSymbolExists(_).isDefined }
      }
    }
  }

  private object TemplateScope {
    def apply(
      index: SemanticdbIndex,
      outerScope: AbstractScope,
      scopeSymbol: Symbol,
      typeParameters: Set[Signature.TypeParameter],
      explicitImports: Seq[ExplicitImport],
      wildcardImports: Seq[WildcardImport]
    ): TemplateScope = new TemplateScope(index, outerScope, scopeSymbol, typeParameters, explicitImports, wildcardImports)
  }

  // ValScope //////////////////////////////////////////////////////////////////////////////////////

  private final class ValScope(
    index: SemanticdbIndex,
    outerScope: AbstractScope,
    scopeSymbol: Symbol
  ) extends AbstractScope(index, Some(outerScope), scopeSymbol) {
    /**
     * Unlike def statments, val and var statements do not contain any
     * additional local bindings of type or value variales.
     *
     * @param signature
     * @return
     */
    override protected def matchingDefinitionFromCurrentScope(
      signature: Signature
    ): Option[Symbol] = None
  }

  private object ValScope {
    def apply(
      index: SemanticdbIndex,
      outerScope: AbstractScope,
      scopeSymbol: Symbol,
    ): ValScope = new ValScope(index, outerScope, scopeSymbol)
  }

  // DefScope //////////////////////////////////////////////////////////////////////////////////////

  private final class DefScope(
    index: SemanticdbIndex,
    outerScope: AbstractScope,
    scopeSymbol: Symbol,
    typeParameters: Set[Signature.TypeParameter],
    termParameters: Set[Signature],
  ) extends AbstractScope(index, Some(outerScope), scopeSymbol) {
    /**
     * Find a definition for symbolComponent directly in the current scope.
     * For a `def` statement, that means amongst the typeParameters and
     * (value) termParameters.
     *
     * @param signature
     * @return
     */
    override protected def matchingDefinitionFromCurrentScope(
      signature: Signature
    ): Option[Symbol] = signature match {
      case signature: Signature.TypeParameter if typeParameters.contains(signature) =>
        Some(Symbol.Global(scopeSymbol, signature))
      case _ if termParameters.contains(signature) =>
        Some(Symbol.Global(scopeSymbol, signature))
      case _ =>
        None
    }
  }

  private object DefScope {
    def apply(
      index: SemanticdbIndex,
      outerScope: AbstractScope,
      scopeSymbol: Symbol,
      typeParameters: Set[Signature.TypeParameter],
      termParameters: Set[Signature],
    ): DefScope = new DefScope(index, outerScope, scopeSymbol, typeParameters, termParameters)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Scope builders: given a Tree, calculate the Scope in effect at its point
  // in the larger Source tree of which it is a subtree.
  //

  /**
   * Builds a scope object for the specified definition, including the types
   * and values that are in scope at the point in the definition where the
   * return type can be specified.
   *
   * This is currently the only public scope builder method because it is the
   * only one that needs to be called for use in ExplicitResultTypes.
   *
   * @param index
   * @param defn
   * @return
   */
  def getScopeForDefn(index: SemanticdbIndex, defn: Defn): Scope = {
    defn match {
      //
      // ValScope
      //
      case Defn.Val(mods, pats, decltpe, rhs) =>
        val outerScope = getOuterScopeBeforeTree(index, defn)
        val scopeSymbol = index.symbol(defn).get
        ValScope(index, outerScope, scopeSymbol)
      case Defn.Var(mods, pats, decltpe, rhs) =>
        val outerScope = getOuterScopeBeforeTree(index, defn)
        val scopeSymbol = index.symbol(defn).get
        ValScope(index, outerScope, scopeSymbol)
      //
      // DefScope
      //
      case Defn.Def(mods, name, tparams, paramss, decltpe, body) =>
        val outerScope = getOuterScopeBeforeTree(index, defn)
        val scopeSymbol = index.symbol(defn).get
        val typeParameters = tparams.map { tparam =>
          Signature.TypeParameter(tparam.name.value) }.toSet
        val parameters = paramss.flatMap { params =>
          params.map { param => Signature.TermParameter(param.name.value): Signature }
        }.toSet
        DefScope(index, outerScope, scopeSymbol, typeParameters, parameters)
    }
  }

  /**
   * Builds a Scope object for the specified tree, only incorporating those
   * imports that occur before the specified subtree.
   *
   * Assuming subtree is a child of tree,
   *   getScopeForTreeBeforeSubtree(index, tree, subtree)
   * is equivalent to
   *   getOuterScopeBeforeTree(index, subtree)
   * i.e., the returned Scope object can be used to resolve what is in scope
   * at the location of subtree.
   *
   * TODO: caching
   *
   * @param index
   * @param tree
   * @param subtree
   * @return
   */
  private def getScopeForTreeBeforeSubtree(
    index: SemanticdbIndex,
    tree: Tree,
    subtree: Tree
  ): AbstractScope = {
    tree match {
      //
      // SourceFileScope
      //
      case Source(stats) => SourceFileScope.notInAnyPackage(index)
      case Pkg(ref, stats) =>
        val scopeSymbol = Symbol(index.symbol(ref).get.syntax)
        val imports = getImportsBeforeSubtree(stats, subtree)
        val explicitImports = getExplicitImports(index, imports)
        val wildcardImports = getWildcardImports(index, imports)
        SourceFileScope(index, scopeSymbol, explicitImports, wildcardImports)
      //
      // TemplateScope
      //
      case Defn.Class(mods, name, tparams, ctor, templ) =>
        getScopeForTemplateBeforeSubtree(index, tree, tparams, templ, subtree)
      case Defn.Object(mods, name, templ) =>
        getScopeForTemplateBeforeSubtree(index, tree, List.empty, templ, subtree)
      case Defn.Trait(mods, name, tparams, ctor, templ) =>
        getScopeForTemplateBeforeSubtree(index, tree, tparams, templ, subtree)
      case templ: Template =>
        // a Template is nested inside of a Class, Object or Trait, so just go
        // up the tree, but pass the same subtree rather than using templ as
        // the subtree.
        templ.parent.map {
          getScopeForTreeBeforeSubtree(index, _, subtree)
        }.getOrElse { SourceFileScope.notInAnyPackage(index) }
      case _ =>
        // Don't know how to handle this, just use the scope from the parent
        getScopeForTreeBeforeSubtree(index, tree.parent.get, tree)
    }
  }

  /**
   * Helper method for getScopeForTreeBeforeSubtree()
   *
   * @param index
   * @param tree
   * @param tparams
   * @param templ
   * @param subtree
   * @return
   */
  private def getScopeForTemplateBeforeSubtree(
    index: SemanticdbIndex,
    tree: Tree,
    tparams: List[Type.Param],
    templ: Template,
    subtree: Tree
  ): AbstractScope = {
    val outerScope = getOuterScopeBeforeTree(index, tree)
    val scopeSymbol = Symbol(index.symbol(tree).get.syntax)
    val typeParameters = tparams.map { tparam => Signature.TypeParameter(tparam.name.value) }.toSet
    val imports = getImportsBeforeSubtree(templ.stats, subtree)
    val explicitImports = getExplicitImports(index, imports)
    val wildcardImports = getWildcardImports(index, imports)
    TemplateScope(index, outerScope, scopeSymbol, typeParameters, explicitImports, wildcardImports)
  }

  /**
   * Gets the outer scope for a tree, i.e., the scope that is in effect right
   * before the tree in its parent.
   *
   * @param index
   * @param tree
   * @return
   */
  private def getOuterScopeBeforeTree(index: SemanticdbIndex, tree: Tree): AbstractScope = {
    tree.parent.map {
      getScopeForTreeBeforeSubtree(index, _, tree)
    }.getOrElse { SourceFileScope.notInAnyPackage(index) }
  }

  /**
   *
   * Given a list of statements, one of which is the specified subtree, returns
   * all of the import statements before the specified subtree.
   *
   * @param stats
   * @param subtree
   * @return
   */
  private def getImportsBeforeSubtree(stats: Seq[Stat], subtree: Tree): Seq[Import] = {
    stats
      .takeWhile(_ != subtree)
      .collect { case i: Import => i }
  }

  /**
   * Given a Seq of Imports, extracts the explicit imports, producing a mapping
   * from Signature (an unqualified name with some kind information) to Symbol
   * (an absolute dotted path to a specific type or value).
   *
   * @param index
   * @param imports
   * @return
   */
  private def getExplicitImports(
    index: SemanticdbIndex,
    imports: Seq[Import]
  ): Seq[ExplicitImport] = {
    // One implementation of Symbol is Symbol.Multi, which contains a list of
    // Symbols. This function expands out both Multi and non-Multi Symbols to
    // a Seq of non-Multi Symbols.
    def expandSymbolMulti(symbol: Symbol): Seq[Symbol] = symbol match {
      case Symbol.Multi(symbols) => symbols.flatMap(expandSymbolMulti)
      case symbol: Symbol => Seq(symbol)
    }

    // Iterate over each of the imports. (A compound import statement that
    // contains a list of symbols to import is visited once per symbol.)
    for (
      Import(importers) <- imports;
      importer <- importers;
      importee <- importer.importees;
      symbolOrSymbols <- index.symbol(importee).toSeq;  // Won't compile unless we convert Option to Seq
      symbol <- expandSymbolMulti(symbolOrSymbols);
      // `PartialFunction.condOpt(x) { cases }` is like `x match { cases }`
      // except it returns an Option, with None if there is no match
      explicitImports <- PartialFunction.condOpt(importee) {
        // Normal case: non-renaming import
        case importee: Importee.Name =>
          symbol match {
            case Symbol.Global(owner, signature) => ExplicitImport(symbol, signature)
          }
        // Renaming imports
        case Importee.Rename(name, Name(rename)) =>
          symbol match {
            case Symbol.Global(owner, signature) => signature match {
              case Signature.Type(name) => ExplicitImport(symbol, Signature.Type(rename))
              case Signature.Term(name) => ExplicitImport(symbol, Signature.Term(rename))
              case Signature.Package(name) => ExplicitImport(symbol, Signature.Package(rename))
              case Signature.Method(name, disambiguator) =>
                ExplicitImport(symbol, Signature.Method(rename, disambiguator))
              case Signature.TypeParameter(name) => ExplicitImport(symbol, Signature.TypeParameter(rename))
              case Signature.TermParameter(name) => ExplicitImport(symbol, Signature.TermParameter(rename))
            }
          }
        // Wildcards and Unimports are not explicit imports; they are handled
        // separately in getWildcardImports()
      }
    ) yield explicitImports
  }

  /**
   * Given a Seq of Imports, extracts the absolute dotted paths to the packages
   * or objects from which there are wildcard imports, along with any
   * corresponding unimports.
   *
   * @param index
   * @param imports
   * @return
   */
  private def getWildcardImports(
    index: SemanticdbIndex,
    imports: Seq[Import]
  ): Seq[WildcardImport] = {
    for (
      Import(importers) <- imports;
      importer <- importers if importer.importees.contains(Importee.Wildcard);
      symbol <- index.symbol(importer.ref);
      unimports = importer.importees.collect {
        case Importee.Unimport(name) => name
      }.toSet
    ) yield {
      assert(!symbol.isInstanceOf[Symbol.Multi])
      WildcardImport(symbol, unimports)
    }
  }
}
