import { connect } from 'react-redux'
import ImplicationLine from '../../components/BaseCase/ImplicationLine'

const mapStateToProps = (state, ownProps) => {

  const getJustificationLine = (just) => {
    switch (just.type) {
      case "LOGICAL_IMPLICATION":
        return "by " + just.by.map(i => state.proof[i].lineNo).join(", ")

      case "ASSUMPTION_CLOSURE":
        return "by ass. closure on " + state.proof[just.antecedant].lineNo + 
          ", " + state.proof[just.consequent].lineNo

      default:
        return "unsupported"
    }
  }

  return {
    justification: getJustificationLine(ownProps.justification)
  }
}

const mapDispatchToProps = (dispatch) => (
  {

  }
)

const RImplicationLine = connect(
  mapStateToProps,
  mapDispatchToProps
)(ImplicationLine)

export default RImplicationLine

