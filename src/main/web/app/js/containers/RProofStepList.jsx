import { connect } from 'react-redux'
import JustifiedFormulaList from '../components/JustifiedFormulaList'

const mapStateToProps = (state) => (
  {
    formulas:
      state.proofSteps.map(({ derived, justification }) => (
          {
            ...state.knownFormulas[derived],
            justification: justification.map((id) => state.knownFormulas[id].uiId)
          }
      ))
  }
)

const RProofStepList = connect(
  mapStateToProps
)(JustifiedFormulaList)

export default RProofStepList

