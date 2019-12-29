import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class FileTest : StringSpec ({
	"success"{
		val (model, repos) = load(Paths.get("src/test/resources/success.abs"))
		val classDecl = model.extractClassDecl("Success","C", repos)
		classDecl.executeAll(repos) shouldBe true
	}
	"fails"{
		val (model, repos) = load(Paths.get("src/test/resources/fail.abs"))
		val classDecl = model.extractClassDecl("Fail","C", repos)

		val iNode = classDecl.extractInitialNode()
		executeNode(iNode, repos) shouldBe false

		for(m in classDecl.methods){
			val node = classDecl.extractMethodNode(m.methodSig.name, repos)
			executeNode(node, repos) shouldBe false
		}
	}
	"create"{
		val (model, repos) = load(Paths.get("src/test/resources/create.abs"))
		val classDecl = model.extractClassDecl("Create","C", repos)

		val iNode = classDecl.extractInitialNode()
		executeNode(iNode, repos) shouldBe true

		val sNode = classDecl.extractMethodNode("success", repos)
		executeNode(sNode, repos) shouldBe true

		val fNode = classDecl.extractMethodNode("fail", repos)
		executeNode(fNode, repos) shouldBe false

		val mNode = model.exctractMainNode()
		executeNode(mNode, repos) shouldBe true
	}
})