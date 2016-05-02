import { connect } from 'react-redux'
import FormulaInput from '../components/FormulaInput'
import { addProofStep } from '../actions'

const mapStateToProps = () => ({})

const mapDispatchToProps = (dispatch) => (
  {
    onEnterPress: (value) => dispatch(addProofStep(value, []))
  }
)

const RAddProofStep = connect(
  mapStateToProps,
  mapDispatchToProps
)(FormulaInput)

export default RAddProofStep

